import ntac.statement


meta inductive semantic_tree : Type
| assume_prop : expr → semantic_tree → semantic_tree
| assume_val : expr → expr → semantic_tree → semantic_tree
| but_false : semantic_tree → semantic_tree
| assume_exist : expr → semantic_tree → semantic_tree
| have_exact : expr → semantic_tree → semantic_tree
| have_from : semantic_tree → semantic_tree → semantic_tree
| let_from : semantic_tree → semantic_tree → semantic_tree
| have_triv : expr → semantic_tree
| suffice_from : expr → semantic_tree → semantic_tree → semantic_tree
| exact : expr → semantic_tree
| trivial : semantic_tree
| unresolved : semantic_tree
| contra : semantic_tree → semantic_tree
| init : semantic_tree → semantic_tree

meta def semantic_tree_to_list_statement : semantic_tree → list statement :=
λ s,match s with
| semantic_tree.trivial := [statement.trivial]
| semantic_tree.suffice_from p s := "dfdfd"
| semantic_tree.have_from p v s := "df"
| _ := "fg"
  end