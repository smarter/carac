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
  private val splitProgram = SplitProgram()

  override protected def sourcesRequired = false

  override protected def newCompiler(using Context): Compiler = new Compiler:
    override protected def frontendPhases: List[List[Phase]] =
      super.frontendPhases :+ List(splitProgram)

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

class SplitProgram extends MacroTransform with IdentityDenotTransformer:
  def phaseName: String = "splitProgram"

  private[storage] var preProcessing: Option[Program] = None
  private[storage] var postProcessing: Option[Program] = None

  def clear(): Unit =
    preProcessing = None
    postProcessing = None
  
  protected def newTransformer(using Context): Transformer =
    val writeIntAsBESym =
      staticRef("datalog.storage.Utils.writeIntAsBE".toTermName).symbol
    val inSym = staticRef("java.lang.System.in".toTermName).symbol
    val outSym = staticRef("java.lang.System.out".toTermName).symbol
    val printlnSym = outSym.requiredMethod("println", List(defn.StringType))
    val writeSym = outSym.requiredMethod("write", List(defn.IntType))

    /// The vals in the current scope whose rhs are instances of Reader wrapping `System.in`.
    var readers: immutable.Set[Symbol] = scala.collection.immutable.LinkedHashSet.empty

    // The vars in the current scope who were assigned a call to `readLine()` from `currentReaderSym`
    var readLines: immutable.Set[Symbol] = scala.collection.immutable.LinkedHashSet.empty

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
        case b @ Block(stats, expr) =>
          val oldReaders = readers
          val oldReadLines = readLines
          try
            for 
          finally
            readers = oldReaders
            readLines = oldReadLines

          super.transform(b)
        case _ =>
          super.transform(tree)

