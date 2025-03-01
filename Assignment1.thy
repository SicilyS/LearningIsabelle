theory Assignment1
imports Main
begin
(*lemmas are in no particular order*)
lemma "\<lbrakk> p \<and> q; r \<rbrakk> \<Longrightarrow> q \<and> r"
  apply(erule conjE)
  apply(erule conjI)
  apply assumption
  done

lemma "A \<longrightarrow> A"
  apply(rule impI)
  apply assumption
  done
 
lemma "((A \<or> B)\<or> C) \<longrightarrow> A \<or> (B \<or>C)"
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
	apply (rule disjI1)
	apply assumption
   apply (rule disjI2)
   apply (rule disjI1)
   apply assumption
  apply (rule disjI2)
  apply (rule disjI2)
  apply assumption
  done

lemma "(A \<longrightarrow> B \<longrightarrow> C)\<longrightarrow> (A \<longrightarrow> B)\<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (erule impE)
   apply (assumption)
  by (erule impE)



lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)
  apply (rule impI)
  apply assumption
  done

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
   apply (rule conjI)
    apply (erule disjE)
     apply assumption
    apply assumption
   apply (erule disjE)
    apply assumption
   apply assumption
  apply (rule disjI1)
  apply (erule conjE)
  apply assumption
  done

lemma "(A \<and> B)\<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (rule disjI1)
  apply (erule conjE)
  apply assumption
  done 

lemma "\<not>\<not>A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longrightarrow> B)\<longrightarrow> (B \<longrightarrow> C)\<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done


lemma "A \<longrightarrow> \<not>\<not>A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done
  


lemma "(\<not>A \<longrightarrow> B)\<longrightarrow> (\<not>B \<longrightarrow> A)"
  apply (rule impI)
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply (erule impE)
   apply assumption
  apply assumption
  done


lemma "(\<not>(A \<and> B)) = (\<not>A \<or> \<not>B)"
  apply (rule iffI)
  apply (rule classical)
   apply (rule disjI2)
   apply (rule classical)
   apply (erule notE)
   apply (erule notE)
   apply (rule classical)
   apply (erule notE)
   apply (erule notE)
  apply (erule disjE)
  sorry



lemma "A \<or> \<not>A"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
  apply assumption
  apply (erule notE)
  apply assumption
  done
   
   


end


