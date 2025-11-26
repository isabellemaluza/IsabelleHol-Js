theory Exponenciacao
  imports Complex_Main
begin

lemma pow_mult_add:
  fixes a :: "'a::semiring_1"
  shows "a ^ n * a ^ k = a ^ (n + k)"
  by (simp add: power_add)

value "(2::real) ^ 3 * 2 ^ 4"       
value "(2::real) ^ (3 + 4)"       
value "(5::real) ^ 1 * 5 ^ 2"       
value "(5::real) ^ (1 + 2)"
value "(3::real) ^ 0 * 3 ^ 5"  
value "(3::real) ^ (0 + 5)"       
value "(2::real) ^ 2 * 2 ^ 3" 
value "(2::real) ^ (2 + 3)"   

end
