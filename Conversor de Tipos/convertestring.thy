theory convertestring
  imports Main
begin

fun is_true :: "string \<Rightarrow> bool" where
  "is_true s = (s = ''True'')"

value "is_true ''True''"   
value "is_true ''False''" 

end
