theory StackMachine2
  imports Main
begin

datatype expr = Const nat | Add expr expr

fun eval_stack :: "expr \<Rightarrow> nat list \<Rightarrow> nat list" where
  "eval_stack (Const n) s = n # s" |
  "eval_stack (Add e1 e2) s = (
      case eval_stack e2 (eval_stack e1 s) of
        x # y # xs \<Rightarrow> (x + y) # xs
      | xs \<Rightarrow> xs
    )"

value "eval_stack (Add (Const 2) (Const 3)) []"
value "eval_stack (Add (Add (Const 1) (Const 2)) (Const 4)) []"
value "eval_stack (Add (Const 10) (Add (Const 2) (Const 3))) []"
value "eval_stack (Const 1) []"

end
