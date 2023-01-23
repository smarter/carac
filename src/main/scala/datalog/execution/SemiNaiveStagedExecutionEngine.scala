package datalog.execution

import datalog.execution.ast.ASTNode
import datalog.execution.ir.*
import datalog.storage.StorageManager
import datalog.tools.Debug.debug

class SemiNaiveStagedExecutionEngine(storageManager: StorageManager) extends StagedExecutionEngine(storageManager) {
  import storageManager.EDB
  override def createIR(ast: ASTNode)(using InterpreterContext): IROp = IRTreeGenerator().generateSemiNaive(ast)
}