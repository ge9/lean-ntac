import ntac.semantic_tree

meta inductive goal_tree : Type
| unres : expr → goal_tree
| unres_andthen : expr → goal_tree

| exact : expr → goal_tree
| assumption : expr → goal_tree
| rewrite : goal_tree → goal_tree
| simp2 : (list expr) → goal_tree → goal_tree
| simp : goal_tree → goal_tree
| skip : goal_tree → goal_tree
| intro : (name × expr) → goal_tree → goal_tree
| have_ : expr → goal_tree → goal_tree
| willhave : goal_tree → goal_tree → goal_tree
| admit : goal_tree
| done : goal_tree
| triv :goal_tree → goal_tree
| contra :goal_tree → goal_tree
| existsi : expr → goal_tree → goal_tree
| apply : expr → list (goal_tree × expr) → goal_tree
| case : list (goal_tree × expr) → goal_tree
| init : list (goal_tree × expr) → goal_tree
| andthen : goal_tree →list (expr × goal_tree) → goal_tree

-- meta def juststr (s: string): goal_tree := goal_tree.tact [([], λ _,s)]
-- meta def goal_tree1 (g: goal_tree) (f: string → string): goal_tree := goal_tree.tact [g] (λ p, 
-- match p with 
-- | h::[]  := f h
-- |_ := "error!"
-- end)
-- meta def addtact (g: goal_tree) (s: string) := goal_tree1 g (λ st, st ++ s)

meta def replc_unres :expr → goal_tree → goal_tree → goal_tree := 
λ e g_new g_org,
match g_org with
| goal_tree.unres e2 := if e = e2 then g_new else g_org
| goal_tree.unres_andthen e2 := if e = e2 then g_new else g_org

| goal_tree.skip g := goal_tree.skip $ replc_unres e g_new g
| goal_tree.simp2 ln g := goal_tree.simp2 ln $ replc_unres e g_new g
| goal_tree.simp g := goal_tree.simp $ replc_unres e g_new g
| goal_tree.triv g := goal_tree.triv $ replc_unres e g_new g
| goal_tree.existsi e g := goal_tree.existsi e $ replc_unres e g_new g
| goal_tree.willhave g1 g2 := goal_tree.willhave (replc_unres e g_new g1) (replc_unres e g_new g2)
| goal_tree.case gl := goal_tree.case $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| goal_tree.contra g := goal_tree.contra $ replc_unres e g_new g
| goal_tree.init gl := goal_tree.init $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| goal_tree.apply ee gl := goal_tree.apply ee $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| goal_tree.andthen g gl := goal_tree.andthen g $ list.map (λ p,let (a, b):= p in (a, (replc_unres e g_new) b)) gl
| _ := g_org
end

meta def to_string2 : expr → string :=
λ e,match e with
| `(%%a ∧ %%b) := (to_string a)++"∧"++(to_string b)
| _ := to_string e
end

meta def goal_tree_to_semantic_tree : goal_tree → semantic_tree :=


meta def goal_tree_to_string : goal_tree → string :=
λ g, match g with
| goal_tree.unres e :=  " *unres* :"++e.to_string
| goal_tree.unres_andthen e :=  " *unres andthen* :"++e.to_string
| goal_tree.admit := "sorry"
| goal_tree.intro (n, e) g := "INTRO " ++ to_string n ++ ":" ++ to_string e ++ "(" ++ (goal_tree_to_string g) ++ ")"
| goal_tree.have_ e g := "have" ++ "<" ++ e.to_string ++ ">" ++"and"++ "<" ++ (goal_tree_to_string g) ++ ">"
| goal_tree.willhave newg oldg := "will have" ++ "<" ++ (goal_tree_to_string newg) ++ ">" ++"and"++ "<" ++ (goal_tree_to_string oldg) ++ ">"
| goal_tree.done := "done"
| goal_tree.exact e:= "exact " ++e.to_string 
| goal_tree.triv g:= "triv (" ++goal_tree_to_string g ++ ")"
| goal_tree.existsi e g:= "exists (" ++ e.to_string ++ "and indeed"++goal_tree_to_string g ++ ")"
| goal_tree.assumption e:= "assumption " ++e.to_string 
| goal_tree.contra g:= "contradiction (" ++ goal_tree_to_string g ++")"
| goal_tree.rewrite g:= "rw (" ++ goal_tree_to_string g ++")"
| goal_tree.simp2 ln g:= "simp by "++string.join (list.map to_string ln) ++"(" ++ goal_tree_to_string g ++")" 
| goal_tree.simp g:= "simp (" ++ goal_tree_to_string g ++")" 
| goal_tree.skip g:= "skip (" ++ goal_tree_to_string g ++ ")"
| goal_tree.apply ee gl := 
let sl := @list.map (goal_tree × expr) string (λ p, let (a, b) := p in "("++(to_string b) ++":" ++(goal_tree_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) ("apply <" ++ee.to_string ++"> and from[") sl in
str ++ "]"
| goal_tree.case gl := 
let sl := @list.map (goal_tree × expr) string (λ p, let (a, b) := p in "("++(to_string b) ++":" ++(goal_tree_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) "case[" sl in
str ++ "]"
  
| goal_tree.init gl := 
let sl := @list.map (goal_tree × expr) string (λ p, let (a, b) := p in "("++
--(to_string2 b) ++
":" ++(goal_tree_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) "init[" sl in
str ++ "]"
| goal_tree.andthen tac1 tac2 :=
let str1 := goal_tree_to_string tac1 in
let sl := @list.map (expr × goal_tree) string (λ p, let (a, b) := p in "("++(to_string a) ++" → " ++(goal_tree_to_string b)++")") tac2 in
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

