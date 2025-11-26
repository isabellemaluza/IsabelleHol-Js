theory Potencias2
  imports Complex_Main
begin

lemma pow_mult_add_manual:
  fixes a :: "'a::semiring_1"
  shows "a ^ n * a ^ k = a ^ (n + k)"
proof (induction n)
  case 0
  then show ?case
  proof -
    have "a ^ 0 * a ^ k = 1 * a ^ k" by simp
    also have "... = a ^ k" by simp
    also have "... = a ^ (0 + k)" by simp
    finally show "a ^ 0 * a ^ k = a ^ (0 + k)" .
  qed


(*
next
  case (Suc n)
  then show ?case
  proof -
    have "a ^ Suc n * a ^ k = (a ^ n * a) * a ^ k" by simp
    also have "... = a ^ n * (a * a ^ k)" by (simp add: mult_assoc)
    also have "... = a ^ n * a ^ Suc k" by simp
    also have "... = a ^ (n + Suc k)" using Suc.IH by simp
    also have "... = a ^ (Suc n + k)" by simp
    finally show ?thesis .
  qed
qed
*)

(* Testes com values *)
value "(2::real) ^ 3 * 2 ^ 4"        (* 128 *)
value "(2::real) ^ (3 + 4)"          (* 128 *)

value "(5::real) ^ 1 * 5 ^ 2"        (* 125 *)
value "(5::real)^ (1 + 2)"          (* 125 *)

value "(3::real) ^ 0 * 3 ^ 5"        (* 243 *)
value "(3::real) ^ (0 + 5)"          (* 243 *)

end
