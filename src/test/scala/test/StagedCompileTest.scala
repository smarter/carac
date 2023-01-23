package test

import datalog.dsl.{Constant, Program, Term}
import datalog.execution.{JoinIndexes, SemiNaiveStagedExecutionEngine}
import datalog.execution.ast.ASTNode
import datalog.execution.ir.*
import datalog.storage.{CollectionsStorageManager, StorageManager}
import datalog.tools.Debug.debug

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.quoted.{Expr, Quotes, staging}
import scala.util.matching.Regex

class StagedCompileTest extends munit.FunSuite {
  val storageManager = new CollectionsStorageManager()
  val engine = new SemiNaiveStagedExecutionEngine(storageManager)
  val program = new Program(engine)
  val edge = program.relation[Constant]("edge")
  val edb = program.relation[Constant]("edb")
  val idb = program.relation[Constant]("idb")
  edb("1") :- ()
  val x, y, z = program.variable()
  edb(x, z) :- (edge(x, y), edge(y, z))

  edge("a", "a") :- ()
  edge("a", "b") :- ()
  edge("b", "c") :- ()
  edge("c", "d") :- ()
  edge("a", "1") :- ()

  given irCtx: InterpreterContext = InterpreterContext(storageManager, engine.precedenceGraph, -1)
  val sVar = "stagedSm"
  val noop = "[\\s\\S]*stagedSm.EDB()[\\s\\S]*"
  val any = "[\\s\\S]*?"
  val anyCapture = "([\\s\\S]*?)"

  // TODO: string compare prob too brittle but ok for dev
  def compileCheck(miniprog: IROp, check: (String => String)*): CollectionsStorageManager => storageManager.EDB = {
    debug("MINI PROG\n", () => storageManager.printer.printIR(miniprog))

    given staging.Compiler = staging.Compiler.make(getClass.getClassLoader)
    val compiled: CollectionsStorageManager => storageManager.EDB =
      staging.run {
        val res: Expr[CollectionsStorageManager => Any] =
          '{ (stagedSm: CollectionsStorageManager) => ${engine.compileIR[collection.mutable.ArrayBuffer[IndexedSeq[Term]]](miniprog)(using 'stagedSm)} }
        val strRes = res.show
        println("STR RES=" + strRes)
        check.foldLeft(strRes)((generatedString, op) =>
          op(generatedString)
        )
        res
      }.asInstanceOf[CollectionsStorageManager => storageManager.EDB]
    compiled
  }
  def generalMatch(test: Regex)(generatedString: String): String =
    generatedString match {
      case test(rest, _*) =>
        println("found test, rest=" + rest)
        rest
      case _ =>
        assert(false, s"generated code '$generatedString' missing expr '$test")
        generatedString
    }

  def whileMatch(cond: String)(generatedString: String): String =
    val whileR = raw"[\s\S]*\{\s+while \(\{([\s\S]*)}\) \(\)([\s\S]*)".r
    generatedString match {
      case whileR(body, noop) =>
        assert(body.trim().endsWith(cond), s"generated code '${body.trim()}' missing cond $cond")
        body
      case _ =>
        assert(false, s"generated code '$generatedString' missing while statement")
        generatedString
    }

  def deepClone(toClone: mutable.Map[Int, storageManager.FactDatabase]): mutable.Map[Int, storageManager.FactDatabase] =
    val derivedClone = mutable.Map[Int, storageManager.FactDatabase]()
    toClone.foreach((k, factdb) => {
      derivedClone(k) = storageManager.FactDatabase()
      factdb.foreach((edbId, edb) =>
        derivedClone(k)(edbId) = storageManager.EDB()
        edb.foreach(e => derivedClone(k)(edbId).append(e))
      )
    })
    derivedClone

  test("DoWhile") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)
    storageManager.resetDerived(idb.id, irCtx.newDbId, storageManager.EDB(Vector("1", "1", "1")))

    println("SM: " + storageManager.printer.toString())
    val toRun = compileCheck(
      DoWhileOp(
        SequenceOp(Seq(
          InsertOp(idb.id, DB.Derived, KNOWLEDGE.Known, ScanOp(idb.id, DB.Derived, KNOWLEDGE.Known), Some(ScanEDBOp(edb.id))), // empty => "1"
          DebugNode("in loop!", () => storageManager.printer.toString()))),
        DB.Derived
      ),
      whileMatch(s"$sVar.compareDerivedDBs(${irCtx.newDbId}, ${irCtx.knownDbId}).unary_!")
    )
//    toRun(storageManager)
  }

  test("SwapOp") {
    val oldKnown = irCtx.knownDbId
    val oldNew = irCtx.newDbId
    val toRun = compileCheck(
      SequenceOp(Seq(
        ScanOp(idb.id, DB.Derived, KNOWLEDGE.Known),
        SwapOp(),
        ScanOp(idb.id, DB.Derived, KNOWLEDGE.Known)
      )),
      generalMatch(s"$any$sVar.derivedDB.apply\\($oldKnown\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r),
      generalMatch(s"$any$sVar.derivedDB.apply\\($oldNew\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r)
    )
    assertNotEquals(oldNew, irCtx.newDbId)
    assertNotEquals(oldKnown, irCtx.knownDbId)
  }

  test("SeqOp") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)
    val toRun = compileCheck(
      SequenceOp(Seq(
        InsertOp(idb.id, DB.Derived, KNOWLEDGE.New, ScanEDBOp(edb.id)),
        InsertOp(idb.id, DB.Delta, KNOWLEDGE.New, ScanEDBOp(edb.id)),
      )),
      generalMatch(s"$any$sVar.resetDerived\\(${idb.id}, ${irCtx.newDbId}, $sVar.edbs.apply\\(${edb.id}\\), $sVar.EDB\\(\\)\\)$anyCapture".r),
      generalMatch(s"$any$sVar.resetDelta\\(${idb.id}, ${irCtx.newDbId}, $sVar.edbs.apply\\(${edb.id}\\)\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.newDbId)(idb.id), ArrayBuffer(Vector("1")))
    assertEquals(storageManager.deltaDB(irCtx.newDbId)(idb.id), ArrayBuffer(Vector("1")))

    storageManager.derivedDB.clear()
    storageManager.deltaDB.clear()
    derived.foreach((k, v) => storageManager.derivedDB(k) = v)
    delta.foreach((k, v) => storageManager.deltaDB(k) = v)
  }

  test("ClearOp") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)

    storageManager.resetDerived(idb.id, irCtx.newDbId, storageManager.EDB(Vector("NewDerived")))
    storageManager.resetDelta(idb.id, irCtx.newDbId, storageManager.EDB(Vector("NewDelta")))

    val toRun = compileCheck(
      ClearOp(),
      generalMatch(s"$any$sVar.clearDB\\(true, ${irCtx.newDbId}\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.newDbId)(idb.id), ArrayBuffer.empty)
    assertEquals(storageManager.deltaDB(irCtx.newDbId)(idb.id), ArrayBuffer(Vector("NewDelta")))

    storageManager.derivedDB.clear()
    storageManager.deltaDB.clear()
    derived.foreach((k, v) => storageManager.derivedDB(k) = v)
    delta.foreach((k, v) => storageManager.deltaDB(k) = v)
  }

  test("ScanEDBOp") {
    val toRun = compileCheck(
      ScanEDBOp(edge.id),
      generalMatch(s"$any$sVar.edbs.apply\\(${edge.id}\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), storageManager.edbs(edge.id))
    val toRun2 = compileCheck(
      ScanEDBOp(-1),
      generalMatch(s"$any$sVar.EDB\\(\\)$anyCapture".r)
    )
    assertEquals(toRun2(storageManager), storageManager.EDB())
  }

  test("ScanOp") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)

    storageManager.resetDerived(idb.id, irCtx.knownDbId, storageManager.EDB(Vector("KnownDerived")))
    storageManager.resetDelta(idb.id, irCtx.knownDbId, storageManager.EDB(Vector("KnownDelta")))
    storageManager.resetDerived(idb.id, irCtx.newDbId, storageManager.EDB(Vector("NewDerived")))
    storageManager.resetDelta(idb.id, irCtx.newDbId, storageManager.EDB(Vector("NewDelta")))

    var toRun = compileCheck(
      ScanOp(idb.id, DB.Derived, KNOWLEDGE.Known),
      generalMatch(s"$any$sVar.derivedDB.apply\\(${irCtx.knownDbId}\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("KnownDerived")))
    toRun = compileCheck(
      ScanOp(idb.id, DB.Delta, KNOWLEDGE.Known),
      generalMatch(s"$any$sVar.deltaDB.apply\\(${irCtx.knownDbId}\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("KnownDelta")))
    toRun = compileCheck(
      ScanOp(idb.id, DB.Derived, KNOWLEDGE.New),
      generalMatch(s"$any$sVar.derivedDB.apply\\(${irCtx.newDbId}\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("NewDerived")))
    toRun = compileCheck(
      ScanOp(idb.id, DB.Delta, KNOWLEDGE.New),
      generalMatch(s"$any$sVar.deltaDB.apply\\(${irCtx.newDbId}\\).getOrElse\\[$any\\]\\(${idb.id}, $sVar\\.EDB\\(\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("NewDelta")))
    toRun = compileCheck(
      ScanOp(edge.id, DB.Derived, KNOWLEDGE.New),
      generalMatch(s"$any$sVar.edbs.apply\\(${edge.id}\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), storageManager.edbs(edge.id))

    storageManager.derivedDB.clear()
    storageManager.deltaDB.clear()
    derived.foreach((k, v) => storageManager.derivedDB(k) = v)
    delta.foreach((k, v) => storageManager.deltaDB(k) = v)
  }

  test("JoinOp") {
    val scanEdge = s"$sVar.edbs.apply\\(${edge.id}\\)"
    val toRun = compileCheck(
      JoinOp(
        Seq(ScanEDBOp(edge.id), ScanEDBOp(edge.id)),
        JoinIndexes(
          Seq(Seq(1, 2)), Map[Int, Constant](0 -> "b"), Seq.empty, Seq.empty
        )
      ),
      generalMatch(s"$any$sVar.joinHelper\\($scanEdge, $scanEdge, $anyCapture".r)
    )

    assertEquals(toRun(storageManager), ArrayBuffer(Vector("b", "c", "c", "d")))
  }

  test("ProjectOp") {
    val scanEdge = s"$sVar.edbs.apply\\(${edge.id}\\)"
    val toRun = compileCheck(
      ProjectOp(
        ScanEDBOp(edge.id),
        JoinIndexes(
          Seq.empty, Map[Int, Constant](), Seq(("c", "1"), ("v", 1)), Seq.empty
        )
      ),
      generalMatch(s"$any$sVar.projectHelper\\($scanEdge, $anyCapture".r)
    )

    assertEquals(toRun(storageManager), ArrayBuffer(Vector("1", "a"), Vector("1", "b"), Vector("1", "c"), Vector("1", "d"), Vector("1", "1")))
  }

  test("InsertOp Delta") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)
    println("start sm=" + storageManager.printer.toString())

    // insert into known, delta from edb
    assertEquals(storageManager.deltaDB(irCtx.knownDbId)(edb.id), ArrayBuffer())
    val scanEdb = s"$sVar.edbs.apply\\(${edb.id}\\)"
    var toRun = compileCheck(
      InsertOp(edb.id, DB.Delta, KNOWLEDGE.Known, ScanEDBOp(edb.id)),
      generalMatch(s"$any$sVar.resetDelta\\(${edb.id}, ${irCtx.knownDbId}, $scanEdb\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.deltaDB(irCtx.knownDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert again to show that it fully resets
    toRun = compileCheck(
      InsertOp(edb.id, DB.Delta, KNOWLEDGE.Known, ScanEDBOp(edb.id)),
      generalMatch(s"$any$sVar.resetDelta\\(${edb.id}, ${irCtx.knownDbId}, $scanEdb\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.deltaDB(irCtx.knownDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert into new, delta from edb
    assertEquals(storageManager.deltaDB(irCtx.newDbId)(edb.id), ArrayBuffer())
    toRun = compileCheck(
      InsertOp(edb.id, DB.Delta, KNOWLEDGE.New, ScanEDBOp(edb.id)), // insert into new, delta from edb
      generalMatch(s"$any$sVar.resetDelta\\(${edb.id}, ${irCtx.newDbId}, $scanEdb\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.deltaDB(irCtx.newDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert again to show that it fully resets
    toRun = compileCheck(
      InsertOp(edb.id, DB.Delta, KNOWLEDGE.New, ScanEDBOp(edb.id)), // insert into new, delta from edb
      generalMatch(s"$any$sVar.resetDelta\\(${edb.id}, ${irCtx.newDbId}, $scanEdb\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.deltaDB(irCtx.newDbId)(edb.id), ArrayBuffer(Vector("1")))

    storageManager.derivedDB.clear()
    storageManager.deltaDB.clear()
    derived.foreach((k, v) => storageManager.derivedDB(k) = v)
    delta.foreach((k, v) => storageManager.deltaDB(k) = v)
  }

  test("InsertOp Derived") {
    val derived = deepClone(storageManager.derivedDB)
    val delta = deepClone(storageManager.deltaDB)
    println("start sm=" + storageManager.printer.toString())

    assertEquals(storageManager.derivedDB(irCtx.knownDbId)(edb.id), ArrayBuffer())
//    assert(storageManager.derivedDB(irCtx.knownDbId).isEmpty)
    // insert into known, derived from edb
    val scanEdb = s"$sVar.edbs.apply\\(${edb.id}\\)"
    val edbS = s"$sVar.EDB\\(\\)"
    var toRun = compileCheck(
      InsertOp(edb.id, DB.Derived, KNOWLEDGE.Known, ScanEDBOp(edb.id)),
      generalMatch(s"$any$sVar.resetDerived\\(${edb.id}, ${irCtx.knownDbId}, $scanEdb, $edbS\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.knownDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert again to show that it fully resets
    toRun = compileCheck(
      InsertOp(edb.id, DB.Derived, KNOWLEDGE.Known, ScanEDBOp(edb.id)),
      generalMatch(s"$any$sVar.resetDerived\\(${edb.id}, ${irCtx.knownDbId}, $scanEdb, $edbS\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.knownDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert into new, derived from edb
    assertEquals(storageManager.derivedDB(irCtx.newDbId)(edb.id), ArrayBuffer())
//    assert(storageManager.derivedDB(irCtx.newDbId).isEmpty) // TODO: why empty and not buffer?
    toRun = compileCheck(
      InsertOp(edb.id, DB.Derived, KNOWLEDGE.New, ScanEDBOp(edb.id)), // insert into new, derived from edb
      generalMatch(s"$any$sVar.resetDerived\\(${edb.id}, ${irCtx.newDbId}, $scanEdb, $edbS\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.newDbId)(edb.id), ArrayBuffer(Vector("1")))

    // insert again to show that it fully resets
    println("after sm=" + storageManager.printer.toString())
    toRun = compileCheck(
      InsertOp(edb.id, DB.Derived, KNOWLEDGE.New, ScanEDBOp(edb.id)), // insert into new, derived from edb
      generalMatch(s"$any$sVar.resetDerived\\(${edb.id}, ${irCtx.newDbId}, $scanEdb, $edbS\\)$anyCapture".r)
    )
    toRun(storageManager)
    assertEquals(storageManager.derivedDB(irCtx.newDbId)(edb.id), ArrayBuffer(Vector("1")))

    storageManager.derivedDB.clear()
    storageManager.deltaDB.clear()
    derived.foreach((k, v) => storageManager.derivedDB(k) = v)
    delta.foreach((k, v) => storageManager.deltaDB(k) = v)
  }

  test("UnionOp") {
    val scanEdge = s"$sVar.edbs.apply\\(${edge.id}\\)"
    val scanEdb = s"$sVar.edbs.apply\\(${edb.id}\\)"
    val toRun = compileCheck(
      UnionOp(Seq(
        ScanEDBOp(edge.id),
        ScanEDBOp(edb.id),
        ScanEDBOp(edb.id)
      )),
      generalMatch(s"$any$sVar.union\\($scanEdge, $scanEdb$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("a", "a"), Vector("a", "b"), Vector("b", "c"), Vector("c", "d"), Vector("a", "1"), Vector("1")))
  }

  test("DiffOp") {
    val scanEdge = s"$sVar.edbs.apply\\(${edge.id}\\)"
    val scanEdb = s"$sVar.edbs.apply\\(${edb.id}\\)"
    val toRun = compileCheck(
      DiffOp(
        ScanEDBOp(edge.id),
        ScanEDBOp(edb.id)
      ),
      generalMatch(s"$any$sVar.getDiff\\($scanEdge, $scanEdb\\)$anyCapture".r)
    )
    assertEquals(toRun(storageManager), ArrayBuffer(Vector("a", "a"), Vector("a", "b"), Vector("b", "c"), Vector("c", "d"), Vector("a", "1")))
  }
}