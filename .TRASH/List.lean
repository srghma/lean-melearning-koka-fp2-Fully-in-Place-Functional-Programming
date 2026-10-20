-- import Lean
-- import Lean.Compiler.IR.Format
--
-- set_option trace.compiler.ir.result true

-- 1. Non-tail-recursive (like std List.length)
def myLength : List α → Nat
  | []      => 0
  | _ :: as => myLength as + 1

-- 2. Tail-recursive (like List.lengthTRAux)
def myLengthTRAux : List α → Nat → Nat
  | [],      acc => acc
  | _ :: as, acc => myLengthTRAux as (acc + 1)

-- #eval show Lean.CoreM Unit from do
--   let env ← Lean.getEnv
--
--   IO.println "=== List.length (Std non-tail-rec) ==="
--   if let some decl := Lean.IR.findEnvDecl env `List.length then
--     IO.println (Lean.IR.declToString decl)
--
--   IO.println "\n=== List.lengthTRAux (Std tail-rec helper) ==="
--   if let some decl := Lean.IR.findEnvDecl env `List.lengthTRAux then
--     IO.println (Lean.IR.declToString decl)
