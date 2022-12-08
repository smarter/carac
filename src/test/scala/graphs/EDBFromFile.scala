package graphs

import datalog.dsl.{Constant, Program, Relation, Term}

import scala.collection.mutable
import java.nio.file.{Files, Path, Paths}
import scala.io.Source
import scala.jdk.StreamConverters.*
//import scala.quoted.*
//import scala.quoted.staging.*

abstract trait TestIDB {
  def run(program: Program): Unit
  val skipNaive = false // for tests that will run out of memory for naive, so skip
}

case class EDBFromFile(program: Program, directory: Path) extends TestGraph {
  val description: String = directory.getFileName.toString
  val queries: mutable.Map[String, Query] = mutable.Map[String, Query]()

  // import EDBs
  private val factdir = Paths.get(directory.toString, "facts")
  if (!Files.exists(factdir)) throw new Exception(f"Missing fact directory '$factdir'")

  Files.walk(factdir, 1)
    .filter(p => Files.isRegularFile(p))
    .forEach(f => {
      val edbName = f.getFileName.toString.replaceFirst("[.][^.]+$", "")
      val fact = program.relation[Constant](edbName)

      val reader = Files.newBufferedReader(f)
      var line: String = null
      while ({line = reader.readLine(); line != null}) {
        fact(line.split("\t"): _*) :- ()
      }
      reader.close()
    })

  // define IDBs
  private val classz = this.getClass.getClassLoader.loadClass(s"graphs.$description")
  private val constr = classz.getConstructor()
  private val idbProgram = constr.newInstance().asInstanceOf[TestIDB]

  idbProgram.run(program)

  // Generate queries
  private val expDir = Paths.get(directory.toString, "expected")
  if (!Files.exists(expDir)) throw new Exception(s"Missing expected directory '$expDir'")
  Files.walk(expDir, 1)
    .filter(p => Files.isRegularFile(p) && p.toString.endsWith(".csv"))
    .forEach(f => {
      val rule = f.getFileName.toString.replaceFirst("[.][^.]+$", "")
      val reader = Files.newBufferedReader(f)
      val res = reader.lines()
        .map(l => l.split("\t").map(s => s.asInstanceOf[Term]).toSeq)
        .toScala(Set)
      queries(rule) = Query(
        rule,
        program.namedRelation[Constant](rule),
        res,
        idbProgram.skipNaive
      )
      reader.close()
    })
}
