package datalog.storage

import dotty.tools.dotc.*
import transform.MacroTransform
import transform.MegaPhase.*
import core.Denotations.staticRef
import core.DenotTransformers.*
import core.Symbols.*
import core.Contexts.*
import core.Flags.*
import core.Decorators.*
import core.StdNames.nme
import core.Names.*
import core.NameKinds.TempResultName
import core.Constants.*
import core.Phases.*
import util.ClasspathFromClassloader
import reporting.*
import dotty.tools.io.VirtualFile
import util.Store
import dotty.tools.uncheckedNN
import ast.tpd.*
import compiletime.uninitialized

import scala.collection.mutable

import java.nio.ByteOrder
import java.nio.file.Paths

sealed trait Program:
  val inputMD: Metadata
  val outputMD: Metadata
case class Command(
  command: List[String], override val inputMD: Metadata, override val outputMD: Metadata
) extends Program
enum Builtin(override val inputMD: Metadata, override val outputMD: Metadata) extends Program:
  /** Big-Endian Ints => CSV. */
  case BEIntToCSV extends Builtin(Metadata.Binary(4, ByteOrder.BIG_ENDIAN), Metadata.CSV)
  /** CSV => Big-Endian Ints. */
  case CSVToBEInt extends Builtin(Metadata.CSV, Metadata.Binary(4, ByteOrder.BIG_ENDIAN))

class ScalaCompiler extends Driver:
  private val pointsTo = PointsTo()
  private val splitProgram = SplitProgram(pointsTo)

  override protected def sourcesRequired = false

  override protected def newCompiler(using Context): Compiler = new Compiler:
    override protected def frontendPhases: List[List[Phase]] =
      super.frontendPhases ++ List(List(pointsTo), List(splitProgram))

  /** Compile `content` into one or more programs. */
  def compileFromCode(mainClass: String, content: String, inputMD: Metadata, outputMD: Metadata): List[Program] =
    val fileName = mainClass
    val file = VirtualFile(fileName, content.getBytes)
    val outputDir = Paths.get("./scala-out").toAbsolutePath.toString
    val currentClasspath = ClasspathFromClassloader(getClass.getClassLoader)
    val args = Array(
      "-classpath", currentClasspath,
      "-d", outputDir
    )
    given Context = setup(args, initCtx.fresh).get._2
    val res = doCompile(newCompiler, List(file))
    if res.hasErrors then
      res.printSummary()
    val commandInputMD = splitProgram.preProcessing.lastOption.map(_.outputMD).getOrElse(inputMD)
    val commandOutputMD = splitProgram.postProcessing.headOption.map(_.inputMD).getOrElse(outputMD)
    val programs =
      splitProgram.preProcessing.toList ++ List(
        Command(
          List("java", "-classpath", s"$currentClasspath:$outputDir", mainClass),
          inputMD = commandInputMD,
          outputMD = commandOutputMD
        )
      ) ++ splitProgram.postProcessing.toList
    splitProgram.clear()
    programs

object Utils:
  def writeIntAsBE(x: Int): Unit =
    val array = Array[Byte](
      ((x >> 24) & 0xFF).toByte,
      ((x >> 16) & 0xFF).toByte,
      ((x >> 8) & 0xFF).toByte,
      (x & 0xFF).toByte,
    )
    System.out.write(array, 0, array.length)

class PointsTo extends MacroTransform with IdentityDenotTransformer:
  def phaseName: String = "localPointsTo"

  import datalog.execution.*
  import datalog.dsl.{Constant, Program}
  val jo = JITOptions()
  val engine = new StagedExecutionEngine(new DefaultStorageManager(), jo)
  object PointsToProgram:
    val program = Program(engine)
    // `pNew(x, constr, arg)` means that
    // `val x = new constr(arg)`
    val pNew = program.relation[Int]("pNew")

    // `pSelect(x, qual, name)` means that
    // `val x = qual.name`
    val pSelect = program.relation[Int]("pSelect")

    // `pAssign(x, qual, receiver, args*)` means that
    // `x = qual.receiver(args*)`
    val pAssign = program.relation[Int]("pAssign")

    // `pCall(x, qual, receiver, args*)` means that
    // `val x = qual.receiver(args*)`
    val pCall = program.relation[Int]("pCall")

    val AssignReadLine = program.relation[Int]("AssignReadLine")
    // IntFromString(x, str) means that val x = Integer.valueOf(str)
    val IntFromString = program.relation[Int]("IntFromString")

    val WrappedNew = program.relation[Int]("WrappedNew")
    val w, x, y, z, constr = program.variable()
    WrappedNew(x, constr, y) :- pNew(x, constr, y)
    WrappedNew(x, constr, y) :- (pNew(x, constr, z), WrappedNew(z, w, y))
  import PointsToProgram.*

  private val idToSymbolMap: mutable.Map[Int, Symbol] = mutable.LinkedHashMap.empty
  def idToSymbol(id: Int): Symbol = idToSymbolMap(id)

  private def toId(sym: Symbol): Int =
    idToSymbolMap(sym.id) = sym
    sym.id
  private def toId(tree: Tree)(using Context): Int = toId(tree.symbol)

  protected def newTransformer(using Context): Transformer =
    // val valueOfSym = defn.BoxedIntModule.requiredMethod("valueOf".toTermName, List(defn.StringType))
    new Transformer:
      override def transform(tree: Tree)(using Context): Tree =
        tree match
          // val ... = new constr(arg)
          case ValDef(_, _, Apply(constr @ Select(New(_), nme.CONSTRUCTOR), List(arg))) =>
            pNew(toId(tree), toId(constr), toId(arg)) :- ()
          case Assign(lhs: Ident, Apply(receiver @ Select(qual: RefTree, _), args)) if args.forall(_.isInstanceOf[RefTree]) =>
            val argsIds = args.map(toId)
            val allParams = toId(lhs) :: toId(qual) :: toId(receiver) :: argsIds
            pAssign(allParams*) :- ()
          case ValDef(_, _, Apply(receiver @ Select(qual: RefTree, _), args)) if args.forall(_.isInstanceOf[RefTree]) =>
            val argsIds = args.map(toId)
            val allParams = toId(tree) :: toId(qual) :: toId(receiver) :: argsIds
            pCall(allParams*) :- ()
          // val ... = Integer.valueOf(str)
          // case ValDef(_, _, Apply(fun, List(str: RefTree))) if fun.symbol == valueOfSym =>
          //   IntFromString(toId(tree), toId(str)) :- ()
          // case v: ValDef =>
          // case v: Assign =>
          //   println("a: " + v)
          case _ =>
        super.transform(tree)

class SplitProgram(pointsTo: PointsTo) extends MacroTransform with IdentityDenotTransformer:
  def phaseName: String = "splitProgram"

  private[storage] var preProcessing: Option[Program] = None
  private[storage] var postProcessing: Option[Program] = None

  def clear(): Unit =
    preProcessing = None
    postProcessing = None
  
  protected def newTransformer(using Context): Transformer =
    import pointsTo.PointsToProgram.*
    import pointsTo.idToSymbol

    val writeIntAsBESym =
      staticRef("datalog.storage.Utils.writeIntAsBE".toTermName).symbol
    val inSym = staticRef("java.lang.System.in".toTermName).symbol
    val outSym = staticRef("java.lang.System.out".toTermName).symbol
    val printlnSym = outSym.requiredMethod("println", List(defn.StringType))
    val writeSym = outSym.requiredMethod("write", List(defn.IntType))
    val valueOfSym = defn.BoxedIntModule.requiredMethod("valueOf".toTermName, List(defn.StringType))

    val bufferedReaderSym = staticRef("java.io.BufferedReader".toTypeName).symbol
    val readLineSym = bufferedReaderSym.requiredMethod("readLine", Nil)

    val WrappedInput = program.relation[Int]("WrappedInput")
    WrappedInput(x, constr) :- WrappedNew(x, constr, inSym.id)

    val wrappedInputIds = WrappedInput.solve().asInstanceOf[Set[Seq[Int]]]
      .filter:
         case Seq(_, constr) => idToSymbol(constr).enclosingClass.derivesFrom(bufferedReaderSym)
      // .map:
      //   case Seq(valDef, _) => idToSymbol(valDef)

    // AssignReadLineFromInput(x) means that
    //     var x = ...
    //     x = y.readLine()
    // where `val y` is a `Reader` that wraps `System.in`
    val AssignReadLineFromInput = program.relation[Int]("AssignReadLineFromInput")
    AssignReadLineFromInput(x) :-
      (pAssign(x, y, readLineSym.id), WrappedInput(y, w, z))

    // ReadLineToInt(x, y) means that
    //     val x = Integer.valueOf(y)
    // where AssignReadLineFromInput(y)
    val ReadLineToInt = program.relation[Int]("ReadLineToInt")
    ReadLineToInt(x, y) :-
      (pCall(x, w, valueOfSym.id, y), AssignReadLineFromInput(y))

    val (toInts, readLines) = ReadLineToInt.solve()
      .asInstanceOf[Set[Seq[Int]]]
      .unzip(tup => (idToSymbol(tup(0)), idToSymbol(tup(1))))

    val assignReadLineFromInputSyms =
      AssignReadLineFromInput.solve().asInstanceOf[Set[Seq[Int]]]
        .map(tup => idToSymbol(tup.head))

    println("wrappedInput: " + wrappedInputIds)
    println("p: " + pAssign.solve())
    // println("AssignReadLineFromInput: " + AssignReadLineFromInput.solve())
    println("assignReadLineFromInputSyms: " + assignReadLineFromInputSyms)
    println("r: " + ReadLineToInt.solve())

    // val pointsTo.program.relation[Int]

    new Transformer:
      // FIXME: for correctness, we need to guarantee that we've identified
      // everything that writes to the standard output.
      override def transform(tree: Tree)(using Context): Tree = tree match
        case Apply(fun, List(Apply(Select(qual, name), Nil)))
        if fun.symbol == printlnSym
        && name == nme.toString_
        && (qual.tpe <:< defn.IntType) =>
          // Factor out conversion in a separate program
          assert(postProcessing.isEmpty, postProcessing)
          postProcessing = Some(Builtin.BEIntToCSV)
          // Rewrite System.out.println(x.toString) to
          // Utils.writeIntAsBE(x)
          ref(writeIntAsBESym).appliedTo(qual)
        // case Assign(lhs: Ident, _) if assignReadLineFromInputSyms.contains(lhs.symbol) =>
        case Assign(lhs: Ident, _) if readLines.contains(lhs.symbol) =>
          // Drop the call to readLine
          Assign(lhs, Literal(Constant(null)))
        case _ =>
          super.transform(tree)

