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

import java.nio.file.Paths

sealed trait Program
case class Command(command: List[String]) extends Program
enum Builtin extends Program:
  /** Little-Endian Ints => ASCII. */
  case IntToAscii

class ScalaCompiler extends Driver:
  private val splitProgram = SplitProgram()

  override protected def sourcesRequired = false

  override protected def newCompiler(using Context): Compiler = new Compiler:
    override protected def frontendPhases: List[List[Phase]] =
      super.frontendPhases :+ List(splitProgram)

  /** Compile `content` into one or more programs. */
  def compileFromCode(mainClass: String, content: String): List[Program] =
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
    val programs =
      splitProgram.preProcessing.toList ++
      List(Command(List(
        "java", "-classpath", s"$currentClasspath:$outputDir", mainClass
      ))) ++ splitProgram.postProcessing.toList
    splitProgram.clear()
    programs

object Utils:
  def printIntAsLE(x: Int): Unit =
    val array = Array[Byte](
      (x & 0xFF).toByte,
      ((x >> 8) & 0xFF).toByte,
      ((x >> 16) & 0xFF).toByte,
      ((x >> 24) & 0xFF).toByte
    )
    System.out.write(array, 0, array.length)
    System.out.println()

class SplitProgram extends MacroTransform with IdentityDenotTransformer:
  def phaseName: String = "splitProgram"

  private[storage] var preProcessing: Option[Program] = None
  private[storage] var postProcessing: Option[Program] = None

  def clear(): Unit =
    preProcessing = None
    postProcessing = None
  
  protected def newTransformer(using Context): Transformer =
    val printIntAsLESym =
      staticRef("datalog.storage.Utils.printIntAsLE".toTermName).symbol
    val outSym = staticRef("java.lang.System.out".toTermName).symbol
    val printlnSym = outSym.requiredMethod("println", List(defn.StringType))
    val writeSym = outSym.requiredMethod("write", List(defn.IntType))
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
          postProcessing = Some(Builtin.IntToAscii)
          // Rewrite System.out.println(x.toString) to
          // Utils.printIntAsLE(x)
          ref(printIntAsLESym).appliedTo(qual)
        case _ =>
          super.transform(tree)

