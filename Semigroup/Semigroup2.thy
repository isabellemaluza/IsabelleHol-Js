theory Semigroup2
  imports Main
begin

section \<open>Definição de Associatividade\<close>

definition is_assoc :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_assoc f \<equiv> (\<forall>x y z. f (f x y) z = f x (f y z))"

section \<open>Provas para Naturais\<close>

lemma add_nat_assoc: "is_assoc ((+) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
proof (unfold is_assoc_def, intro allI)
  fix x y z :: nat
  show "(x + y) + z = x + (y + z)"
    by simp
qed

lemma mult_nat_assoc: "is_assoc ((*) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
proof (unfold is_assoc_def, intro allI)
  fix x y z :: nat
  show "(x * y) * z = x * (y * z)"
    by simp
qed

section \<open>Exemplo de operação NÃO associativa\<close>

lemma sub_nat_not_assoc: "\<not> is_assoc ((-) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
proof -
  have "((3::nat) - 2) - 1 \<noteq> (3 - (2 - 1))"
    by simp   \<comment> \<open>(3 - 2) - 1 = 0, mas 3 - (2 - 1) = 2\<close>
  then show ?thesis
    unfolding is_assoc_def by blast
qed

lemma add_zero_right [simp]: "x + 0 = (x :: nat)"
  by simp

lemma mult_one_right [simp]: "x * 1 = (x :: nat)"
  by simp


value "((1::nat) + 2) + 3"
value "(1::nat) + (2 + 3)"
value "((5::nat) + 7) + 9"
value "(5::nat) + (7 + 9)"

value "((2::nat) * 3) * 4"
value "(2::nat) * (3 * 4)"
value "((0::nat) * 7) * 8"
value "(0::nat) * (7 * 8)"

value "((3::nat) - 2) - 1"
value "(3::nat) - (2 - 1)"
value "((10::nat) - 4) - 2"
value "(10::nat) - (4 - 2)"
value "((5::nat) - 8) - 2"
value "(5::nat) - (8 - 2)" 


end