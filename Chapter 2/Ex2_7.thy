theory Ex2_7
  imports Main
begin

datatype 'a tree2 = Leaf 'a | Node "'a tree2" "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf v) = Leaf v" |
"mirror (Node l r) = Node (mirror l) (mirror r)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf v) = [v]" |
"pre_order (Node l r) = (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf v) = [v]" |
"post_order (Node l r) = (post_order r) @ (post_order l)"

theorem mirror_order : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

end