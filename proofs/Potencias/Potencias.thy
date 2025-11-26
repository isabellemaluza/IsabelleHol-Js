theory Potencias
  imports Complex_Main
begin

lemma pow_zero_nat: "n ^ 0 = (1 :: nat)"
  by simp

lemma pow_one_nat: "n ^ 1 = (n :: nat)"
  by simp

lemma pow_one_nat_explicit: "n ^ 1 = (n :: nat)"
proof -
  have "n ^ 1 = n ^ Suc 0" by simp
  also have "... = n * (n ^ 0)" by (simp add: power_Suc)
  also have "... = n * 1" by (simp add: pow_zero_nat)
  also have "... = n" by simp
  finally show ?thesis .
qed

lemma pow_zero_int: "x ^ 0 = (1 :: int)"
  by simp

lemma pow_one_int: "x ^ 1 = (x :: int)"
  by simp

lemma pow_zero_real: "x ^ 0 = (1 :: real)"
  by simp

lemma pow_one_real: "x ^ 1 = (x :: real)"
  by simp


lemma power_zero_gen: "a ^ 0 = (1 :: 'a::{power,one})"
  by simp

lemma power_one_gen: "a ^ 1 = (a :: 'a::{power,semiring_1})"
  by simp


value "(5::nat) ^ 0"     
value "(7::nat) ^ 1"     
value "(-3::int) ^ 0"  
value "(-3::int) ^ 1" 
value "(2::real) ^ 0"  
value "(2::real) ^ 1"  

end