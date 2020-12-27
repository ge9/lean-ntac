import ntac.semantic_tree

meta structure type_info := (type: expr) (kind: expr)
meta structure named_expr := (name: name) (type: expr) (kind: expr)
meta structure named_expr_value := (name: name) (type: expr) (kind: expr) (value: expr)

meta mutual inductive goal_info ,goal_tree
with goal_info :Type 
| mk : type_info → goal_tree → goal_info
with goal_tree : Type
| unres : expr → goal_tree
| unres_andthen : expr → goal_tree

| exact : expr → goal_tree
| assumption : expr → goal_tree
| rewrite : goal_info → goal_tree
| simp2 : (list expr) → goal_info → goal_tree
| simp : option goal_info → goal_tree
| skip : goal_info → goal_tree
| intro : (name × expr) → goal_info → goal_tree
| have_ : named_expr_value → goal_info → goal_tree
| define : expr → expr → goal_info → goal_tree
| willhave : named_expr → goal_info → goal_info → goal_tree
| willdefine : expr → goal_info → goal_info → goal_tree
| suffice : named_expr → goal_info → goal_info → goal_tree
| admit : goal_tree
| done : goal_tree
| triv :goal_info → goal_tree
| contra :goal_info → goal_tree
| existsi : expr → goal_info → goal_tree
| apply : expr → list goal_info → goal_tree
| case : list goal_info → goal_tree
| init : goal_info → goal_tree
| andthen : goal_tree →list (expr × goal_info) → goal_tree

-- meta def juststr (s: string): goal_tree := goal_tree.tact [([], λ _,s)]
-- meta def goal_tree1 (g: goal_tree) (f: string → string): goal_tree := goal_tree.tact [g] (λ p, 
-- match p with 
-- | h::[]  := f h
-- |_ := "error!"
-- end)
-- meta def addtact (g: goal_tree) (s: string) := goal_tree1 g (λ st, st ++ s)

meta def replc_unres :expr → goal_tree → goal_tree → goal_tree := 
λ e g_new g_org,
let rep_info : goal_info → goal_info := (λ gi, match gi with | goal_info.mk ty g := goal_info.mk ty (replc_unres e g_new g) end)
in
match g_org with
| goal_tree.unres e2 := if e = e2 then g_new else g_org
| goal_tree.unres_andthen e2 := if e = e2 then g_new else g_org
| goal_tree.skip g := goal_tree.skip $ rep_info g
| goal_tree.simp2 ln g := goal_tree.simp2 ln $ rep_info g
| goal_tree.simp (some g) := goal_tree.simp $ rep_info g
| goal_tree.rewrite g := goal_tree.rewrite $ rep_info g
| goal_tree.triv g := goal_tree.triv $ rep_info g
| goal_tree.existsi e g := goal_tree.existsi e $ rep_info g
| goal_tree.willhave ne g1 g2 := goal_tree.willhave ne (rep_info g1) (rep_info g2)
| goal_tree.suffice ne g1 g2 := goal_tree.suffice ne (rep_info g1) (rep_info g2)
| goal_tree.case gl := goal_tree.case $ list.map rep_info gl
| goal_tree.contra g := goal_tree.contra $ rep_info g
| goal_tree.init g := goal_tree.init $ rep_info g
| goal_tree.apply ee gl := goal_tree.apply ee $ list.map rep_info gl
| goal_tree.andthen g gl := goal_tree.andthen g $ list.map (λ p,let (a, b):= p in (a, (rep_info) b)) gl
| goal_tree.intro ne g := goal_tree.intro ne $  rep_info g
| goal_tree.have_ nev g :=  goal_tree.have_ nev $ rep_info g
| goal_tree.define edef eval g :=  goal_tree.define edef eval $ rep_info g
| goal_tree.willdefine e g1 g2 :=  goal_tree.willdefine e (rep_info g1) (rep_info g2)
| _ := g_org
end

meta def to_string2 : expr → string :=
λ e,match e with
| `(%%a ∧ %%b) := (to_string a)++"∧"++(to_string b)
| _ := to_string e
end

meta def goal_tree_to_semantic_tree : goal_tree → semantic_tree :=
λ g, match g with
| goal_tree.unres _ := semantic_tree.unresolved
| goal_tree.unres_andthen _ := semantic_tree.unresolved
| goal_tree.admit := semantic_tree.unresolved
| goal_tree.intro (n, e) (goal_info.mk a g) := semantic_tree.assume_prop e $ goal_tree_to_semantic_tree g
| goal_tree.have_ ⟨n,t,k,v⟩ (goal_info.mk a g) := semantic_tree.have_exact t $ goal_tree_to_semantic_tree g
| goal_tree.define edef eval (goal_info.mk a g) := semantic_tree.assume_val edef eval $ goal_tree_to_semantic_tree g
| goal_tree.willhave ne (goal_info.mk a newg) (goal_info.mk b oldg) := semantic_tree.have_from (goal_tree_to_semantic_tree newg) (goal_tree_to_semantic_tree oldg) 
| goal_tree.suffice ⟨n,t,k⟩ (goal_info.mk a newg) (goal_info.mk b oldg) := semantic_tree.suffice_from t (goal_tree_to_semantic_tree newg) (goal_tree_to_semantic_tree oldg) 
| goal_tree.willdefine ne (goal_info.mk a newg) (goal_info.mk b oldg) := semantic_tree.let_from (goal_tree_to_semantic_tree newg) (goal_tree_to_semantic_tree oldg) 
| goal_tree.done := semantic_tree.unresolved
| goal_tree.exact e:= semantic_tree.exact e
| goal_tree.triv g:= semantic_tree.trivial
| goal_tree.existsi e (goal_info.mk a g) := semantic_tree.assume_exist e $ goal_tree_to_semantic_tree g
| goal_tree.assumption e:= semantic_tree.exact e
| goal_tree.contra (goal_info.mk a g):= semantic_tree.contra $ goal_tree_to_semantic_tree g
| goal_tree.rewrite g:= semantic_tree.unresolved
| goal_tree.simp2 ln g:= semantic_tree.unresolved
| goal_tree.simp g:= semantic_tree.unresolved
| goal_tree.skip  (goal_info.mk a g):= goal_tree_to_semantic_tree g
| goal_tree.apply ee gl := semantic_tree.unresolved
| goal_tree.case gl := semantic_tree.unresolved
| goal_tree.andthen gl l:= semantic_tree.unresolved
| goal_tree.init (goal_info.mk a g) := semantic_tree.init $ goal_tree_to_semantic_tree g
end


meta def goal_tree_to_string : goal_tree → string :=
let goal_tree_to_string2: goal_info → string := λ gi, match gi with goal_info.mk ty g := goal_tree_to_string g end in
let goal_tree_to_string3: goal_info → string := λ gi, match gi with goal_info.mk ty g := "("++(to_string ty.type) ++"::" ++(goal_tree_to_string g)++")" end in
λ g, match g with
| goal_tree.unres e :=  " *unres* :"++e.to_string
| goal_tree.unres_andthen e :=  " *unres andthen* :"++e.to_string
| goal_tree.admit := "sorry"
| goal_tree.intro (n, e) g := "INTRO " ++ to_string n ++ ":" ++ to_string e ++ "(" ++ (goal_tree_to_string2 g) ++ ")"
| goal_tree.have_ ⟨name, type, kind, val⟩ g := "have " ++ type.to_string ++ "by <"++val.to_string ++">"++"and"++ "<" ++ (goal_tree_to_string2 g) ++ ">"
| goal_tree.define edef eval g := "let " ++ edef.to_string++" := " ++ eval.to_string ++ ">" ++"and"++ "<" ++ (goal_tree_to_string2 g) ++ ">"
| goal_tree.willhave ⟨name, type, kind⟩ newg oldg := "will have " ++ type.to_string ++" from" ++ "<" ++ (goal_tree_to_string2 newg) ++ ">" ++"and"++ "<" ++ (goal_tree_to_string2 oldg) ++ ">"
| goal_tree.suffice ⟨name, type, kind⟩ newg oldg := "suffice " ++ type.to_string ++" from"  ++ "<" ++ (goal_tree_to_string2 newg) ++ ">" ++"and"++ "<" ++ (goal_tree_to_string2 oldg) ++ ">"
| goal_tree.willdefine e newg oldg := "will let" ++ e.to_string++"by" ++ "<" ++ (goal_tree_to_string2 newg) ++ ">" ++"and"++ "<" ++ (goal_tree_to_string2 oldg) ++ ">"
| goal_tree.done := "done"
| goal_tree.exact e:= "exact " ++e.to_string 
| goal_tree.triv g:= "triv (" ++goal_tree_to_string2 g ++ ")"
| goal_tree.existsi e g:= "exists (" ++ e.to_string ++ "and indeed"++goal_tree_to_string2 g ++ ")"
| goal_tree.assumption e:= "assumption " ++e.to_string 
| goal_tree.contra g:= "contradiction (" ++ goal_tree_to_string2 g ++")"
| goal_tree.rewrite g:= "rw (" ++ goal_tree_to_string2 g ++")"
| goal_tree.simp2 ln g:= "simp by "++string.join (list.map to_string ln) ++"(" ++ goal_tree_to_string2 g ++")" 
| goal_tree.simp (some g):= "simp (" ++ goal_tree_to_string2 g ++")" 
| goal_tree.simp none:= "by simp" 
| goal_tree.skip g:= "skip (" ++ goal_tree_to_string2 g ++ ")"
| goal_tree.apply ee gl := 
let sl := list.map goal_tree_to_string3 gl in
let str := list.foldl (λ acc s, acc ++", "++ s) ("apply <" ++ee.to_string ++"> and from[") sl in
str ++ "]"
| goal_tree.case gl := 
let sl := list.map goal_tree_to_string3 gl in
let str := list.foldl (λ acc s, acc ++", "++ s) "case[" sl in
str ++ "]"
  
| goal_tree.init g := "init[" ++ goal_tree_to_string2 g ++ "]"

| goal_tree.andthen tac1 tac2 :=
let str1 := goal_tree_to_string tac1 in
let sl := @list.map (expr × goal_info) string (λ p, let (a, b) := p in "("++(to_string a) ++" → " ++(goal_tree_to_string2 b)++")") tac2 in
let str := list.foldl (λ acc s, acc ++", "++ s) ("do {"++str1++"} and then{") sl in
str ++ "}"
end

meta def for_andthen : goal_tree → goal_tree :=
λ g, match g with
| goal_tree.unres e := goal_tree.unres_andthen e
| _ := g
end

meta instance : has_to_format goal_tree :=
⟨λ g,to_fmt $ goal_tree_to_string g⟩

