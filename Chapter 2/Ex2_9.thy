theory Ex2_9
imports 
    Main
    Ex2_2
begin

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_add : "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

end