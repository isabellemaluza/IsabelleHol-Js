theory HOL_Theorems_Examples
  imports Main
begin

lemma add_commute: "(x + (y :: nat)) = y + x" by simp
value "((2 :: nat) + 3) = (3 + 2)"
value "((0 :: nat) + 5) = (5 + 0)"

lemma add_assoc: "(x + (y :: nat)) + z = x + (y + z)" by simp
value "(((1 :: nat) + 2) + 3) = (1 + (2 + 3))"
value "(((0 :: nat) + 4) + 5) = (0 + (4 + 5))"

lemma add_0_left: "0 + (x :: nat) = x" by simp
value "(0 + (7 :: nat)) = (7 :: nat)"
value "(0 + (0 :: nat)) = (0 :: nat)"

lemma add_0_right: "(x :: nat) + 0 = x" by simp
value "((9 :: nat) + 0) = (9 :: nat)"
value "((0 :: nat) + 0) = (0 :: nat)"

lemma mult_commute: "(x :: nat) * y = y * x" by simp
value "((2 :: nat) * 3) = (3 * 2)"
value "((0 :: nat) * 5) = (5 * 0)"

lemma mult_assoc: "(x :: nat) * y * z = x * (y * z)" by simp
value "(((2 :: nat) * 3) * 4) = (2 * (3 * 4))"
value "(((1 :: nat) * 5) * 6) = (1 * (5 * 6))"

lemma distrib_left: "(x :: nat) * (y + z) = x * y + x * z"
  by (simp add: distrib_left)
value "((2 :: nat) * (3 + 4) = (2 * 3 + 2 * 4)) = True"
value "((1 :: nat) * (5 + 0) = (1 * 5 + 1 * 0)) = True"

lemma conj_commute: "((P :: bool) \<and> (Q :: bool)) = (Q \<and> P)"
  by blast
value "((True \<and> False) = (False \<and> True)) = True"
value "((True \<and> True) = (True \<and> True)) = True"

lemma disj_commute: "((P :: bool) \<or> (Q :: bool)) = (Q \<or> P)"
  by blast
value "((True \<or> False) = (False \<or> True)) = True"
value "((False \<or> False) = (False \<or> False)) = True"

lemma not_conj: "\<not> (P \<and> Q) = (\<not> P \<or> \<not> Q)" by simp
value "((\<not> (True \<and> False)) = ((\<not> True) \<or> (\<not> False)))"
value "((\<not> (False \<and> False)) = ((\<not> False) \<or> (\<not> False)))"

lemma not_disj: "\<not> (P \<or> Q) = (\<not> P \<and> \<not> Q)" by simp
value "((\<not> (True \<or> False)) = ((\<not> True) \<and> (\<not> False)))"
value "((\<not> (False \<or> False)) = ((\<not> False) \<and> (\<not> False)))"

lemma and_True: "(P \<and> True) = P" by simp
value "(((True :: bool) \<and> True) = True)"
value "(((False :: bool) \<and> True) = False)"

lemma or_False: "(P \<or> False) = P" by simp
value "(((True :: bool) \<or> False) = True)"
value "(((False :: bool) \<or> False) = False)"

lemma double_negation: "\<not> (\<not> P) = P" by simp
value "((\<not> (\<not> True)) = True)"
value "((\<not> (\<not> False)) = False)"

lemma eq_sym: "x = (y :: nat) \<Longrightarrow> y = x" by simp
value "((2 :: nat) = (2 :: nat)) \<longrightarrow> ((2 :: nat) = 2)"
value "((0 :: nat) = (0 :: nat)) \<longrightarrow> ((0 :: nat) = 0)"

lemma if_True: "(if True then x else y) = (x :: nat)" by simp
value "((if True then (5 :: nat) else 0) = 5)"
value "((if True then (0 :: nat) else 9) = 0)"

lemma if_False: "(if False then x else y) = (y :: nat)" by simp
value "((if False then (5 :: nat) else 1) = 1)"
value "((if False then (0 :: nat) else 7) = 7)"

lemma zero_less_mult_pos:
  "0 < (x :: nat) \<Longrightarrow> 0 < y \<Longrightarrow> 0 < x * y"
  by (simp add: mult_less_0_iff)
value "(((0 :: nat) < 2 \<and> (0 :: nat) < 3) \<longrightarrow> (0 :: nat) < 2 * 3) = True"
value "(((0 :: nat) < 1 \<and> (0 :: nat) < 5) \<longrightarrow> (0 :: nat) < 1 * 5) = True"

lemma less_trans_example:
  "x < (y :: nat) \<Longrightarrow> y < z \<Longrightarrow> x < z"
  by simp
value "(((1 :: nat) < 2 \<and> (2 :: nat) < 4) \<longrightarrow> (1 :: nat) < 4) = True"
value "(((0 :: nat) < 1 \<and> (1 :: nat) < 3) \<longrightarrow> (0 :: nat) < 3) = True"

lemma less_eq_trans_example:
  "x \<le> (y :: nat) \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  by simp
value "(((1 :: nat) \<le> 2 \<and> (2 :: nat) \<le> 3) \<longrightarrow> (1 :: nat) \<le> 3) = True"
value "(((0 :: nat) \<le> 0 \<and> (0 :: nat) \<le> 5) \<longrightarrow> (0 :: nat) \<le> 5) = True"


lemma impI_blast: "P \<Longrightarrow> (P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> Q)"
  by blast
value "((True \<longrightarrow> True) = True)"
value "((False \<longrightarrow> True) = True)"

lemma impE_blast_simple: "(P \<longrightarrow> Q) \<Longrightarrow> P \<Longrightarrow> Q"
  by blast
value "(((True \<longrightarrow> False) \<longrightarrow> True) = True)"  
value "(((True \<longrightarrow> True) \<and> True) = True)"

lemma conjI_blast: "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  by blast
value "((True \<and> False) = False)"
value "((True \<and> True) = True)"

lemma conjE_blast: "P \<and> Q \<Longrightarrow> P"
  by blast
value "((True \<and> False) \<longrightarrow> True) = True"  
value "((True \<and> True) \<longrightarrow> True) = True"

lemma disjI1_blast: "P \<Longrightarrow> P \<or> Q"
  by blast
value "((True \<longrightarrow> (True \<or> False)) = True)"
value "((False \<longrightarrow> (False \<or> True)) = True)"

lemma disjE_blast: "(P \<or> Q) \<Longrightarrow> (P \<longrightarrow> R) \<Longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> R"
  by blast
value "(((True \<or> False) \<and> (True \<longrightarrow> True) \<and> (False \<longrightarrow> True)) \<longrightarrow> True) = True"
value "(((False \<or> True) \<and> (False \<longrightarrow> False) \<and> (True \<longrightarrow> False)) \<longrightarrow> False) = True"

lemma notI_blast: "(P \<longrightarrow> False) \<Longrightarrow> \<not> P"
  by blast
value "(((True \<longrightarrow> False) \<longrightarrow> (\<not> True)) = True)"
value "(((False \<longrightarrow> False) \<longrightarrow> (\<not> False)) = True)"

lemma notE_blast: "\<not> P \<Longrightarrow> P \<Longrightarrow> False"
  by blast
value "(((\<not> True) \<and> True) \<longrightarrow> False) = True"
value "(((\<not> False) \<and> False) \<longrightarrow> False) = True"

lemma allI_blast: "(\<forall>x::nat. P x) \<Longrightarrow> (\<forall>x::nat. P x)"
  by blast
value "((0 :: nat) = 0) = True"
value "((1 :: nat) = 0) = False"

lemma list_append_assoc: "((xs :: nat list) @ ys) @ zs = xs @ (ys @ zs)" by simp
value "((( [1 :: nat] @ [2]) @ [3]) = ([1] @ ([2] @ [3])))"
value "(((([] :: nat list) @ [1,2]) @ [3]) = ([] @ ([1,2] @ [3])))"

lemma list_append_Nil: "(xs :: nat list) @ [] = xs" by simp
value "((([1 :: nat,2] :: nat list) @ []) = [1,2])"
value "((([] :: nat list) @ []) = [])"

lemma list_rev_append: "rev (xs :: nat list) @ rev ys = rev (ys @ xs)" by simp
value "((rev ([1 :: nat]) @ rev [2]) = rev ([2] @ [1]))"
value "((rev ([] :: nat list) @ rev [1,2]) = rev ([1,2] @ []))"

lemma list_map_append: "map (f :: nat => nat) (xs @ ys) = map f xs @ map f ys" by simp
value "(map (\<lambda>x. x + (1 :: nat)) ([1] @ [2]) = (map (\<lambda>x. x + 1) [1] @ map (\<lambda>x. x + 1) [2]))"
value "(map (\<lambda>x. x * (2 :: nat)) ([] :: nat list) = (map (\<lambda>x. x * 2) [] @ map (\<lambda>x. x * 2) [1]))"

lemma list_map_id: "map (\<lambda>u. u :: nat) (xs :: nat list) = xs" by simp
value "(map (\<lambda>u. u) ([1 :: nat,2]) = [1,2])"
value "(map (\<lambda>u. u) ([] :: nat list) = [])"

lemma nat_add_0_right: "(n :: nat) + 0 = n" by simp
value "(((3 :: nat) + 0) = 3)"
value "(((0 :: nat) + 0) = 0)"

lemma nat_add_0_left: "0 + (n :: nat) = n" by simp
value "(((0 :: nat) + 4) = 4)"
value "(((0 :: nat) + 0) = 0)"

lemma nat_add_commute: "(m :: nat) + n = n + m" by simp
value "(((2 :: nat) + 5) = (5 + 2))"
value "(((0 :: nat) + 7) = (7 + 0))"

lemma nat_add_assoc: "(m :: nat) + n + p = m + (n + p)" by simp
value "((((1 :: nat) + 2) + 3) = (1 + (2 + 3)))"
value "((((0 :: nat) + 4) + 5) = (0 + (4 + 5)))"

end


