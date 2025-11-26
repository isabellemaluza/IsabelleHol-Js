theory StackMachine
  imports Main
begin


datatype expr = Const nat | Add expr expr

datatype instr = Load nat | Write | AddTop


fun exec :: "instr \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat list * nat list)" where
  "exec (Load n) stack out = (n # stack, out)" |
  "exec Write [] out = ([], out)" |
  "exec Write (x # xs) out = (xs, x # out)" |
  "exec AddTop [] out = ([], out)" |               
  "exec AddTop [x] out = ([x], out)" |             
  "exec AddTop (x # y # xs) out = ((x+y) # xs, out)"  


fun run :: "instr list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat list * nat list)" where
  "run [] stack out = (stack, out)" |
  "run (i#is) stack out =
     (let (s', o') = exec i stack out
      in run is s' o')"


fun comp :: "expr \<Rightarrow> instr list" where
  "comp (Const n) = [Load n]" |
  "comp (Add e1 e2) = comp e1 @ comp e2 @ [AddTop]"


fun eval :: "expr \<Rightarrow> nat" where
  "eval e = hd (fst (run (comp e) [] []))"
                         
value "eval (Const 5)"  
value "eval (Add (Const 8) (Const 3))" 
value "comp (Add (Const 10) (Add (Const 1) (Const 2)))" 

end


