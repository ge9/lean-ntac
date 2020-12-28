import ntac.semantic_tree
import ntac.ja

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
| andthen : goal_info →list (expr × goal_info) → goal_tree

meta def destruct_gi (gi: goal_info) : (type_info × goal_tree) :=
match gi with goal_info.mk ti gt :=(ti,gt) end

prefix `##`:30 := destruct_gi

meta def replc_unres :expr → goal_tree → goal_info → goal_info := 
λ e g_new gi_org,
match gi_org  with
| goal_info.mk ty g_org :=
let rep_info : goal_info → goal_info := replc_unres e g_new
--(λ gi, match gi with | goal_info.mk ty g := goal_info.mk ty (replc_unres e g_new g) end)
 in
let gt_new := match g_org with
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
end in 
goal_info.mk ty gt_new
end

meta def to_string2 : expr → string :=
λ e,match e with
| `(%%a ∧ %%b) := (to_string a)++"∧"++(to_string b)
| _ := to_string e
end
meta instance : inhabited goal_info := ⟨goal_info.mk ⟨expr.var 1, expr.var 1⟩ goal_tree.admit⟩
meta def goal_info_to_semantic_tree : goal_info → tactic semantic_tree :=
λ g, let (ti,gt) := ## g in
do 
match gt with
| goal_tree.unres _ := semantic_tree.unresolved
| goal_tree.unres_andthen _ := semantic_tree.unresolved
| goal_tree.admit := semantic_tree.unresolved
| goal_tree.intro (n, e) gi := semantic_tree.assume_prop e $ goal_info_to_semantic_tree gi
| goal_tree.have_ ⟨n,t,k,v⟩ gi  := semantic_tree.have_exact t $ goal_info_to_semantic_tree gi
| goal_tree.define edef eval gi  := semantic_tree.assume_val edef eval $ goal_info_to_semantic_tree gi
| goal_tree.willhave ⟨n,t,k⟩ (goal_info.mk _ $ goal_tree.triv _) oldg := semantic_tree.have_triv t (goal_info_to_semantic_tree oldg) 
| goal_tree.willhave ne newg oldg := semantic_tree.have_from (goal_info_to_semantic_tree newg) (goal_info_to_semantic_tree oldg) 
| goal_tree.suffice ⟨n,t,k⟩ newg oldg := semantic_tree.suffice_from t (goal_info_to_semantic_tree newg) (goal_info_to_semantic_tree oldg) 
| goal_tree.willdefine ne newg oldg := semantic_tree.let_from (goal_info_to_semantic_tree newg) (goal_info_to_semantic_tree oldg) 
| goal_tree.done := semantic_tree.unresolved
| goal_tree.exact e:= semantic_tree.exact e
| goal_tree.triv g:= semantic_tree.trivial
| goal_tree.existsi e gi := semantic_tree.assume_exist e $ goal_info_to_semantic_tree gi
| goal_tree.assumption e:= semantic_tree.exact e
| goal_tree.contra gi:= semantic_tree.contra $ goal_info_to_semantic_tree gi
| goal_tree.rewrite g:= semantic_tree.unresolved
| goal_tree.simp2 ln g:= semantic_tree.unresolved
| goal_tree.simp g:= semantic_tree.unresolved
| goal_tree.skip gi:= goal_info_to_semantic_tree gi
| goal_tree.apply ee gl := match ee with
    | `(Exists.intro %%n) := match ti with | ⟨`(Exists %%d),_⟩ := if (expr.binding_name d) = expr.local_pp_name n then goal_info_to_semantic_tree gl.head else semantic_tree.trivial |_:= semantic_tree.trivial end
    |_ :=semantic_tree.unresolved
  end
| goal_tree.case gl := semantic_tree.unresolved
| goal_tree.andthen gl l:= semantic_tree.unresolved
| goal_tree.init gi := semantic_tree.init $ goal_info_to_semantic_tree gi
end
#check ([1,1] ++ [1,2] )++ [3,2]
meta def join_expr (ts:tactic string) (e:expr ): tactic string :=
do ppe ← tactic.pp e,
s ← ts,
return $ s ++ ppe.to_string
meta def join_expr2 (ts:tactic string) (e:expr ): tactic string :=
do s ← ts,
return $ s ++ e.to_string

meta def join_str :tactic string→ string → tactic string := flip $ λ e, functor.map (++e) 
meta def join_tstr (ts1 : tactic string) (ts2 : tactic string) : tactic string := do 
s1 ← ts1, s2 ← ts2, return (s1++s2)
local infix `+S+`:65 := join_str
local infix `+E+`:65 := join_expr
local infix `+T+`:65 := join_tstr
local prefix `!`:75 := return
meta def goal_tree_to_string : goal_tree → tactic string :=
let goal_tree_to_string2: goal_info → tactic string := λ gi, match gi with goal_info.mk ty g := goal_tree_to_string g end in
let goal_tree_to_string3: goal_info → tactic string := λ gi, match gi with goal_info.mk ty g := do ty ← tactic.pp ty.type,g ← (goal_tree_to_string g),return $ "("++ty.to_string++"::" ++g++")" end in
λ g, match g with
| goal_tree.unres e := !" *unres* :"+E+e
| goal_tree.unres_andthen e := !" *unres andthen* :"+E+e
| goal_tree.admit := !"sorry"
| goal_tree.intro (n, e) g := !"INTRO " +S+ to_string n +S+ ":" +E+ e +S+ "(" +T+ (goal_tree_to_string2 g) +S+ ")"
| goal_tree.have_ ⟨name, type, kind, val⟩ g := !"have " +E+ type +S+ "by <"+E+ val +S+ ">and<" +T+ (goal_tree_to_string2 g) +S+ ">"
| goal_tree.define edef eval g := !"let "+E+ edef +S+" := <" +E+ eval +S+ ">and<" +T+ (goal_tree_to_string2 g) +S+ ">"
| goal_tree.willhave ⟨name, type, kind⟩ newg oldg := !"will have " +E+ type +S+" from<" +T+ (goal_tree_to_string2 newg) +S+ ">and<" +T+ (goal_tree_to_string2 oldg) +S+ ">"
| goal_tree.suffice ⟨name, type, kind⟩ newg oldg := !"suffice " +E+ type +S+" from<" +T+ (goal_tree_to_string2 newg) +S+ ">and<" +T+ (goal_tree_to_string2 oldg) +S+ ">"
| goal_tree.willdefine e newg oldg := !"will let" +E+ e +S+ "by<" +T+ (goal_tree_to_string2 newg) +S+ ">and<" +T+ (goal_tree_to_string2 oldg) +S+ ">"
| goal_tree.done := !"done"
| goal_tree.exact e:= !"exact " +E+ e
| goal_tree.triv g:= !"triv (" +T+ goal_tree_to_string2 g +S+ ")"
| goal_tree.existsi e g:= !"exists (" +E+ e +S+ "and indeed" +T+ goal_tree_to_string2 g +S+ ")"
| goal_tree.assumption e:= !"assumption " +E+ e
| goal_tree.contra g:= !"contradiction (" +T+ goal_tree_to_string2 g +S+")"
| goal_tree.rewrite g:= !"rw (" +T+ goal_tree_to_string2 g +S+")"
| goal_tree.simp2 ln g:= !"simp by "+S+string.join (list.map to_string ln) +S+"(" +T+ goal_tree_to_string2 g +S+")" 
| goal_tree.simp (some g):= !"simp (" +T+ goal_tree_to_string2 g +S+")" 
| goal_tree.simp none:= !"by simp" 
| goal_tree.skip g:= !"skip (" +T+ goal_tree_to_string2 g +S+ ")"
| goal_tree.apply ee gl := 
let sl := list.map goal_tree_to_string3 gl in
let str := list.foldl (λ acc s, acc +S+", "+T+ s) (!"apply <" +E+ee +S+"> and from[") sl in
str +S+ "]"
| goal_tree.case gl := 
let sl := list.map goal_tree_to_string3 gl in
let str := list.foldl (λ acc s, acc +S+", "+T+ s) (!"case[") sl in
str +S+ "]"

| goal_tree.init g := !"init[" +T+ goal_tree_to_string2 g +S+ "]"

| goal_tree.andthen tac1 tac2 :=
let str1 := goal_tree_to_string2 tac1 in
let sl := @list.map (expr × goal_info) (tactic string) (λ p, let (a, b) := p in !"("+E+a +S+" → " +T+(goal_tree_to_string2 b)+S+")") tac2 in
let str := list.foldl (λ acc s, acc +S+", "+T+ s) (!"do {"+T+str1+S+"} and then{") sl in
str +S+ "}"
end

meta def for_andthen : goal_tree → goal_tree :=
λ g, match g with
| goal_tree.unres e := goal_tree.unres_andthen e
| _ := g
end
meta def goal_tree_to_format : goal_tree → tactic format :=
λ g, do str ← goal_tree_to_string g,return $ to_fmt str
meta def goal_info_to_format : goal_info → tactic format :=
λ g, match g with goal_info.mk te gt :=  do str ← goal_tree_to_string gt,
return $ to_fmt str

end
meta def goal_info_to_format2 : goal_info → tactic format :=
λ g, return $ to_fmt $ list.map S_ja $ tolistS $ goal_info_to_semantic_tree $ g
meta instance : has_to_tactic_format goal_info :=
⟨goal_info_to_format⟩

