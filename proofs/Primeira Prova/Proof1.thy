theory Proof1
  imports Main
begin

datatype expr = Const nat | Add expr expr

datatype instr = PUSH nat | ADD

type_synonym stack = "nat list"

fun exec1 :: "instr \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (PUSH n) s = n # s" |
  "exec1 ADD (x # y # s) = (x + y) # s" |
  "exec1 ADD s = s" 

fun exec :: "instr list \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] s = s" |
  "exec (i # is) s = exec is (exec1 i s)"


fun eval :: "expr \<Rightarrow> nat" where
  "eval (Const n) = n" |
  "eval (Add e1 e2) = eval e1 + eval e2"


fun comp :: "expr \<Rightarrow> instr list" where
  "comp (Const n) = [PUSH n]" |
  "comp (Add e1 e2) = comp e1 @ comp e2 @ [ADD]"


lemma exec_append: "exec (xs @ ys) s = exec ys (exec xs s)"
proof (induction xs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i xs)
  then show ?case by simp
qed


lemma comp_correct_strong:
  "exec (comp e @ p) s = exec p (eval e # s)"
proof (induction e arbitrary: s p)
  case (Const n)
  then show ?case by simp
next
  case (Add e1 e2)
  have "exec (comp (Add e1 e2) @ p) s
      = exec ((comp e1 @ comp e2 @ [ADD]) @ p) s" by simp
  also have "... = exec (comp e2 @ [ADD] @ p) (eval e1 # s)"
    using Add.IH(1) by (simp add: exec_append)
  also have "... = exec ([ADD] @ p) (eval e2 # eval e1 # s)"
    using Add.IH(2) by (simp add: exec_append)
  also have "... = exec p ((eval e2 + eval e1) # s)" by simp
  also have "... = exec p ((eval e1 + eval e2) # s)"
    by (simp add: add.commute)
  finally show ?case by simp
qed  

theorem comp_correct:
  "exec (comp e) s = eval e # s"
proof -
  have "exec (comp e @ []) s = exec [] (eval e # s)"
    using comp_correct_strong[of e "[]" s] .
  then show ?thesis by simp
qed

value "exec (comp (Add (Const 2) (Const 3))) []"   
value "exec (comp (Add (Const 2) (Const 3))) [10]"   
value "exec (comp (Add (Const 1) (Add (Const 2) (Const 4)))) []" 


end