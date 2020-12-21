inductive prop : Type
| noun : prop

meta inductive semantic_tree : Type
| assume_prop : expr → semantic_tree → semantic_tree
| assume_var : expr → semantic_tree → semantic_tree
| but_false : semantic_tree → semantic_tree
| assume_exist : expr → semantic_tree → semantic_tree
| have_from : prop → prop → semantic_tree → semantic_tree
| have_triv : prop → semantic_tree
| suffice : prop → semantic_tree → semantic_tree
| trivial : semantic_tree

meta def semantic_tree_to_string : semantic_tree → string :=
λ s,match s with
| semantic_tree.trivial := "gtg"
| semantic_tree.suffice p s := "dfdfd"
| semantic_tree.have_from p v s := "df"
| _ := "fg"
  end