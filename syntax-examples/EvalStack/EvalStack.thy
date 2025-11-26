theory EvalStack
  imports Main
begin

(* Definição do tipo de expressão *)
datatype expr =
  Const nat |
  Add expr expr

(* Avaliação direta da expressão *)
fun sum_expr :: "expr \<Rightarrow> nat" where
  "sum_expr (Const n) = n" |
  "sum_expr (Add e1 e2) = sum_expr e1 + sum_expr e2"

(* Avaliação usando pilha *)
fun eval_stack :: "expr \<Rightarrow> nat list \<Rightarrow> nat list" where
  "eval_stack (Const n) s = n # s" |
  "eval_stack (Add e1 e2) s = (
      let s1 = eval_stack e2 s in
      let s2 = eval_stack e1 s1 in
      (hd s2 + hd (tl s2)) # (tl (tl s2))
    )"

(* Exemplos *)
value "eval_stack (Const 5) []"
value "eval_stack (Add (Const 2) (Const 3)) []"
value "eval_stack (Add (Add (Const 1) (Const 2)) (Const 4)) []"
value "eval_stack (Add (Add (Const 10) (Add (Const 2) (Const 3))) (Const 4)) []"

(* --- LEMAS E PROVAS --- *)

lemma eval_stack_sum:
  "sum_list (eval_stack e s) = sum_expr e + sum_list s"
proof (induction e arbitrary: s)
  case (Const n)
  then show ?case by simp
next
  case (Add e1 e2)
  then show ?case
    by (simp add: Let_def)
qed

lemma eval_stack_empty:
  "eval_stack e [] = [sum_expr e]"
  using eval_stack_sum[of e "[]"] by simp

lemma eval_stack_suffix:
  "\<exists>t. eval_stack e s = t @ s"
proof (induction e arbitrary: s)
  case (Const n)
  then show ?case by simp
next
  case (Add e1 e2)
  obtain t2 where "eval_stack e2 s = t2 @ s" using Add.IH(2) by blast
  obtain t1 where "eval_stack e1 (eval_stack e2 s) = t1 @ (eval_stack e2 s)" using Add.IH(1) by blast
  then show ?case
    using `eval_stack e2 s = t2 @ s` by auto
qed

end

