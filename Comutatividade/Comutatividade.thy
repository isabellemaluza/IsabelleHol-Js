theory Comutatividade
  imports Complex_Main
begin

datatype expr = Const nat | Var string | Plus expr expr
type_synonym memory = "string \<Rightarrow> nat"

fun eval :: "expr \<Rightarrow> memory \<Rightarrow> nat" where
  "eval (Const n) _ = n" |
  "eval (Var x) mem = mem x" |
  "eval (Plus e1 e2) mem = eval e1 mem + eval e2 mem"

datatype instr = PUSH_CONST nat | PUSH_VAR string | ADD

fun compile :: "expr \<Rightarrow> instr list" where
  "compile (Const n) = [PUSH_CONST n]" |
  "compile (Var x) = [PUSH_VAR x]" |
  "compile (Plus e1 e2) = compile e1 @ compile e2 @ [ADD]"

fun exec :: "instr list \<Rightarrow> memory \<Rightarrow> nat list \<Rightarrow> nat list" where
  "exec [] _ stk = stk" |
  "exec (PUSH_CONST n # is) mem stk = exec is mem (n # stk)" |
  "exec (PUSH_VAR x # is) mem stk = exec is mem (mem x # stk)" |
  "exec (ADD # is) mem (x # y # stk) = exec is mem ((y + x) # stk)" |
  "exec (ADD # is) _ stk = []"


lemma exec_append: "exec (p1 @ p2) mem stk = exec p2 mem (exec p1 mem stk)"
proof (induction p1 arbitrary: stk)
  case Nil
  then show ?case by simp
next
  case (Cons a p1)
  then show ?case
  proof (cases a)
    case (PUSH_CONST n)
    then show ?thesis by simp (metis Cons.IH)
  next
    case (PUSH_VAR x)
    then show ?thesis by simp (metis Cons.IH)
  next
    case ADD
  then show ?thesis by (cases stk) (simp_all add: Cons.IH)
  qed
qed

lemma compile_exec_correct:
  "exec (compile e) mem stk = eval e mem # stk"
proof (induction e arbitrary: stk)
  case (Const n)
  then show ?case by simp
next
  case (Var x)
  then show ?case by simp
next
  case (Plus e1 e2)
  then show ?case
    using exec_append Plus.IH by simp
qed

theorem soma_comutativa_memoria:
  "exec (compile (Plus e1 e2)) mem stk = exec (compile (Plus e2 e1)) mem stk"
proof -
  show ?thesis
    by (simp add: exec_append compile_exec_correct add.commute)
qed


definition mem_exemplo :: memory where
  "mem_exemplo x = (if x = ''a'' then 2 else if x = ''b'' then 5 else 0)"

definition prog1 :: expr where
  "prog1 = Plus (Var ''a'') (Var ''b'')"   (* a + b *)

definition prog2 :: expr where
  "prog2 = Plus (Var ''b'') (Var ''a'')"   (* b + a *)

value "compile prog1"
value "compile prog2"

value "exec (compile prog1) mem_exemplo []"
value "exec (compile prog2) mem_exemplo []"

value "eval prog1 mem_exemplo"
value "eval prog2 mem_exemplo"
value "eval prog1 mem_exemplo = eval prog2 mem_exemplo"

end


