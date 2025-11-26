theory DOM_Onclick
  imports Main
begin

datatype event = OnClick | OnChange | OnLoad

type_synonym handler = string

datatype node =
    Element string "((string * string) list)" "node list" "((event * handler) list)"
  | Text string

fun addEventListener :: "event \<Rightarrow> handler \<Rightarrow> node \<Rightarrow> node" where
  "addEventListener ev h (Element name attrs children evs) =
     Element name attrs children ((ev, h) # evs)" |
  "addEventListener ev h (Text t) = Text t"

definition setOnClick :: "handler \<Rightarrow> node \<Rightarrow> node" where
  "setOnClick h n = addEventListener OnClick h n"

definition button0 :: node where
  "button0 = Element ''button'' [( ''id'', ''btn1'')] [] []"

definition button1 :: node where
  "button1 = setOnClick ''showAlert'' button0"


value "button0"  

value "button1"  

value "setOnClick ''logClick'' button1"  

end
