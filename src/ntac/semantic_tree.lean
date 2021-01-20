import ntac.sentence


meta inductive semantic_tree : Type
| assume_prop : string → semantic_tree → semantic_tree
| assume_val : string → string → semantic_tree → semantic_tree
| but_false : semantic_tree → semantic_tree
| assume_exist : string → semantic_tree → semantic_tree
| have_exact : string → string → semantic_tree → semantic_tree
| have_from : semantic_tree → semantic_tree → semantic_tree
| let_from : semantic_tree → semantic_tree → semantic_tree
| have_triv : string → semantic_tree → semantic_tree
| suffice_exact : string → string → semantic_tree → semantic_tree
| suffice_from : string → semantic_tree → semantic_tree → semantic_tree
| exact : string → string → semantic_tree
| from_ : string → semantic_tree
| trivial : semantic_tree
| unresolved : semantic_tree
| contra : semantic_tree → semantic_tree
| init : semantic_tree → semantic_tree

meta def tolistS : semantic_tree → list S :=
λ s,match s with
| semantic_tree.unresolved := [S._unresolved]
| semantic_tree.trivial := [S._trivial]
| semantic_tree.init s := tolistS s
| semantic_tree.suffice_from e t1 t2 :=tolistS t1 ++ Adv._hence /a/ <eNP>e /p/ <VVP>V._suf_show :: tolistS t2
| semantic_tree.suffice_exact e1 e2 t :=Adv._from <NP><eN>e1 /a/ <eNP>e2 /p/ <VVP>V._suf_show :: tolistS t
| semantic_tree.have_from t1 t2 := tolistS t1 ++ tolistS t2
| semantic_tree.have_triv e t2 := Adv._trivially /a/ <eS>e :: tolistS t2
| semantic_tree.assume_prop e t:= /i/ <V2VP>V2._assume <eNP>e :: tolistS t
| semantic_tree.exact e1 e2 := [Adv._from <NP><eN>e1 /a/ <eS>e2]
| semantic_tree.assume_val edef eval t:= /i/ <V3VP> V3._let <NP><eN>edef <NP><eN>eval :: tolistS t
| semantic_tree.assume_exist e t := [S._trivial]
| semantic_tree.have_exact e res t := Adv._from <NP><eN>e /a/ <eS>res :: tolistS t
| semantic_tree.let_from t1 t2 := tolistS t1 ++ tolistS t2
| _ :=[S._trivial]
end