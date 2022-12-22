package examples.fib

import datalog.dsl.{Constant, Program}
import tools.GraphGenerator

import java.nio.file.Paths
class fib extends GraphGenerator(
  Paths.get("src", "test", "scala", "examples", "fib") // TODO: use pwd
) {

  def pretest(program: Program): Unit = {
    val f = program.relation[Constant]("f")
    val succ = program.namedRelation("succ")
    val plus_mod = program.namedRelation("plus_mod")

    val i, r, prev, pprev, x, y = program.variable()

    f("0", "0") :- ()
    f("1", "1") :- ()
    f(i, r) :- ( succ(prev, i), succ(pprev, prev),f(prev, x), f(pprev, y), plus_mod(x, y, r) )
  }
}