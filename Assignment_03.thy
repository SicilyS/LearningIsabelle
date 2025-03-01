theory Assignment_03
  imports Main
begin

thm allE

lemma "\<lbrakk>\<forall>x. (P x \<longrightarrow> Q x); \<forall>x. P x\<rbrakk> \<Longrightarrow> \<forall>x. Q x"
  apply (rule allI)
  apply (erule_tac x = x in allE)
  apply (erule_tac x = x in allE)
  by (erule mp)
(*by applies the rule and then as many assumptions as possible*)

lemma "\<forall>x. P x \<longrightarrow> P x"
  apply (rule allI)
  by (rule impI)

thm allI
thm allE

lemma "(\<forall>x. P \<longrightarrow> Q x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. Q x)"
  apply (rule impI)
  apply (rule allI)
  apply (erule_tac x = x in allE)
  by (erule impE)
    
thm exE
thm exI

lemma "(\<exists>x. P \<and> Q x) \<Longrightarrow> P \<and> (\<exists>x. Q x)"
  apply (rule conjI)
   apply (erule exE)
  apply (erule conjE)
   apply assumption
  apply (erule exE)
  apply (rule_tac x = x in exI)
  by (erule conjE)

lemma "((\<forall>x. F x) \<and> (\<forall>x. G x)) \<longrightarrow> (\<forall>x. F x \<and> G x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x = x in allE)
  apply (rule conjI)
   apply assumption
  by (erule_tac x = x in allE)

lemma "(\<forall>x y. R x y) \<longrightarrow> (\<forall>x. R x x)"
  apply (rule impI)
  apply (rule allI)
  apply (erule_tac x = x in allE)
  by (erule_tac x  = x in allE) 


thm ccontr

lemma "(\<forall>x. P x) \<or> (\<exists>x. \<not>P x)"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule ccontr, erule notE)
  apply (rule disjI2)
  apply (rule ccontr,erule notE)
  apply (rule allI)
  apply (rule ccontr, erule notE)
  by (rule_tac x = x in exI)

lemma "(\<forall>x. \<not>(P x \<longrightarrow> Q x)) \<longrightarrow> \<not>(\<exists>x. \<not>P x \<and> Q x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x = x in allE)
  apply (erule conjE)
  apply (erule notE)
  by (rule impI)
 

lemma "(\<exists>Bob. (drunk Bob \<longrightarrow> (\<forall>x. drunk x)))"
  sorry

thm ccontr
(*break up the if and only if. first direction takes forever*)
(*use by blast to see if steps are in wrong direction*)
lemma "\<not>(\<exists>barber. man barber \<and> (\<forall>x. man x \<and> \<not> shaves x x \<longleftrightarrow> shaves barber x))"
  apply (rule ccontr, erule notE)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule allE)
  apply (erule iffE)
  apply (rule notE)
  
  
  
  by (blast)


  



  apply (erule_tac x = x in allE)

end
