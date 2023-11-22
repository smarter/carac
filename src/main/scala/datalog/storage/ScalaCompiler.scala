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
import core.NameOps.freshened
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
      // "-Xprint:typer,splitProgram",
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
    val array = new Array[Byte](4)
    array(0) = ((x >> 24) & 0xff).toByte
    array(1) = ((x >> 16) & 0xff).toByte
    array(2) = ((x >>  8) & 0xff).toByte
    array(3) = ((x      ) & 0xff).toByte
    System.out.write(array, 0, array.length)

  def readBEAsInt(): Int =
    val array = new Array[Byte](4)
    val res = System.in.read(array, 0, 4)
    if res != 4 then throw new java.io.EOFException
    ((array(0) & 0xff) << 24) +
    ((array(1) & 0xff) << 16) +
    ((array(2) & 0xff) <<  8) +
    ((array(3) & 0xff)      )

class PointsTo extends MacroTransform with IdentityDenotTransformer:
  def phaseName: String = "localPointsTo"

  import datalog.execution.*
  import datalog.dsl.{Constant, Program}
  val jo = JITOptions()
  val engine = new StagedExecutionEngine(new DefaultStorageManager(), jo)
  object PointsToProgram:
    val program = Program(engine)
    /**
     * `pNew(x, constr, arg)` means that
     *     val x = new constr(arg)
     */
    val pNew = program.relation[Int]("pNew")

    /**
     * `pCall(x, qual, receiver, args*)` means that
     * `val x = qual.receiver(args*)`
     */
    val pCall = program.relation[Int]("pCall")

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
    // val parseIntSym = defn.BoxedIntModule.requiredMethod("parseInt".toTermName, List(defn.StringType))
    new Transformer:
      override def transform(tree: Tree)(using Context): Tree =
        tree match
          // val ... = new constr(arg)
          case ValDef(_, _, Apply(constr @ Select(New(_), nme.CONSTRUCTOR), List(arg))) =>
            pNew(toId(tree), toId(constr), toId(arg)) :- ()
          // val ... = receiver(args*)
          case ValDef(_, _, Apply(receiver @ Select(qual: RefTree, _), args)) if args.forall(_.isInstanceOf[RefTree]) =>
            val argsIds = args.map(toId)
            val allParams = toId(tree) :: toId(qual) :: toId(receiver) :: argsIds
            pCall(allParams*) :- ()
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
    val readBEAsIntSym =
      staticRef("datalog.storage.Utils.readBEAsInt".toTermName).symbol
    val inSym = staticRef("java.lang.System.in".toTermName).symbol
    val outSym = staticRef("java.lang.System.out".toTermName).symbol
    val printlnSym = outSym.requiredMethod("println", List(defn.StringType))
    val writeSym = outSym.requiredMethod("write", List(defn.IntType))
    val parseIntSym = defn.BoxedIntModule.requiredMethod("parseInt".toTermName, List(defn.StringType))

    val bufferedReaderSym = staticRef("java.io.BufferedReader".toTypeName).symbol
    val readLineSym = bufferedReaderSym.requiredMethod("readLine", Nil)

    val WrappedInput = program.relation[Int]("WrappedInput")
    WrappedInput(x, constr) :- WrappedNew(x, constr, inSym.id)

    val wrappedInputIds = WrappedInput.solve().asInstanceOf[Set[Seq[Int]]]
      .filter:
         case Seq(_, constr) => idToSymbol(constr).enclosingClass.derivesFrom(bufferedReaderSym)
      // .map:
      //   case Seq(valDef, _) => idToSymbol(valDef)

    /**
     * AssignReadLineFromInput(x) means that
     *     var x = ...
     *     x = y.readLine()
     * where `val y` is a `Reader` that wraps `System.in`
     */
    val AssignReadLineFromInput = program.relation[Int]("AssignReadLineFromInput")
    AssignReadLineFromInput(x) :-
      (pCall(x, y, readLineSym.id), WrappedInput(y, w, z))

    /**
     * ToInt_ReadLine(x, y) means that
     *     val x = Integer.parseInt(y)
     * where AssignReadLineFromInput(y)
     */
    val ToInt_ReadLine = program.relation[Int]("ToInt_ReadLine")
    ToInt_ReadLine(x, y) :-
      (pCall(x, w, parseIntSym.id, y), AssignReadLineFromInput(y))


    val toInts_ReadLines: Map[Symbol, Symbol] = ToInt_ReadLine.solve()
      .asInstanceOf[Set[Seq[Int]]]
      .map:
        case Seq(toInt, readLine) => (idToSymbol(toInt), idToSymbol(readLine))
      .toMap

    val readLines = toInts_ReadLines.values.toSet

    /**
     * A map that gets populated during the transformation, when we observe:
     *
     *     val x = y.readLine()
     *
     * which gets transformed to:
     *
     *     val x = ""
     *     val x$1 = Utils.readBEAsInt()
     *
     * This maps maps `x` to `x$1` to replace usages of `x`.
     */
    val readLineReplacementMap: mutable.Map[Symbol, Symbol] = mutable.Map.empty

    new Transformer:
      // FIXME: for correctness, we need to guarantee that we've identified
      // everything that writes to stdout, read to stdin.
      //
      // Additionally, we're currently assuming that the original code handles
      // EOFException when the input is closed, but this might not be the case.
      override def transform(tree: Tree)(using Context): Tree = tree match

        // Rewrite System.out.println(x.toString) to
        //     Utils.writeIntAsBE(x)
        // and split the conversion in a separate program BEIntToCSV
        case Apply(fun, List(Apply(Select(qual, name), Nil)))
        if fun.symbol == printlnSym
        && name == nme.toString_
        && (qual.tpe <:< defn.IntType) =>
          // Factor out conversion in a separate program
          assert(postProcessing.isEmpty || postProcessing == Some(Builtin.BEIntToCSV), postProcessing)
          postProcessing = Some(Builtin.BEIntToCSV)
          ref(writeIntAsBESym).appliedTo(qual)

        // Rewrite val line = y.readLine() into
        //     val line = ""
        //     val line$1 = Utils.readBEAsInt()
        // and split the conversion in a separate program CSVToBEInt
        case tree: ValDef if readLines.contains(tree.symbol) =>
          assert(preProcessing.isEmpty || preProcessing == Some(Builtin.CSVToBEInt), preProcessing)
          preProcessing =  Some(Builtin.CSVToBEInt)
          val replacement = SyntheticValDef(
            name = tree.name.freshened,
            rhs = ref(readBEAsIntSym).ensureApplied,
            flags = tree.symbol.flags
          )
          readLineReplacementMap(tree.symbol) = replacement.symbol
          Thicket(List(
            cpy.ValDef(tree)(rhs = Literal(Constant(""))),
            replacement
          ))

        // Rewrite val x = Integer.parseInt(line) into
        //     val x = line$1
        case tree: ValDef if toInts_ReadLines.contains(tree.symbol) =>
          val newRhs = ref(readLineReplacementMap(toInts_ReadLines(tree.symbol)))
          cpy.ValDef(tree)(rhs = newRhs)
        case _ =>
          super.transform(tree)

