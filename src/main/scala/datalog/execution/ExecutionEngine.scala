package datalog.execution

import datalog.dsl.{Atom, Term}
import datalog.storage.StorageManager

import scala.collection.mutable.ArrayBuffer

trait ExecutionEngine {
  def initRelation(rId: Int, name: String): Unit

  def insertIDB(rId: Int, rule: Seq[Atom]): Unit
  def insertEDB(body: Atom): Unit

  def solve(rId: Int): Set[Seq[Term]]
  def solveNaive(rId: Int): Set[Seq[Term]]
  //  def insertBulkEDB[T](relationId: Int, terms: Seq[Seq[T]]): Unit = {}
}
