theory Ex2_2
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

theorem add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_zero_left [simp]: "add x 0 = x"
  apply(induction x)
   apply(auto)
  done

lemma add_suc_left [simp]: "add m (Suc n) = Suc(add m n)"
  apply(induction m)
   apply(auto)
  done

theorem add_comm: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

theorem double_is_addmm: "double m = add m m"
  apply(induction m)
   apply(auto)
  done

end