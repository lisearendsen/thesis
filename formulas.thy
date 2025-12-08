(*
    Author: Lise Arendsen, TU/e
*)

section \<open>Proving formulas correct\<close>

theory formulas
imports paths Main
begin

lemma succswitch: 
  assumes "\<forall>s. \<exists> succ. s \<in> S' \<longrightarrow> P s succ"
  shows "\<exists>succ. \<forall>s \<in> S'. P s (succ s)" 
  using assms by metis

subsection \<open>Proposition 40\<close>

lemma proposition40:
  fixes M :: "('a, 's) lts"
  assumes "\<not>dependvar f M 0"
  and "\<not>dependvar g M 0"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "s \<in> \<lbrakk>\<mu> g \<and>\<^sub>\<mu> (f \<or>\<^sub>\<mu> \<langle>Acts A\<rangle>\<^sub>R var 0)\<rbrakk> M e =
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e)"
  (is "s \<in> \<lbrakk>\<mu> ?f\<rbrakk> M e = ?R s")                   
proof
  have "mono (transformer ?f M e)" by (rule monotonicitynotdependcoro(1); simp add: notdepends assms)
  moreover assume "s \<in> \<lbrakk>mu ?f\<rbrakk> M e"                               
  ultimately have "s \<in> ((transformer ?f M e)^^(card (UNIV :: 's set))){}" using assms(3) transformer_eq_mu by metis
  moreover {
    fix n
    have "s \<in> ((transformer ?f M e)^^n){} \<longrightarrow> ?R s"
      apply (induct n arbitrary: s)       
      apply simp
    proof
      fix n s
      assume IH: "\<And>s. s \<in> (transformer ?f M e ^^ n) {} \<longrightarrow> ?R s"
      assume assum1: "s \<in> (transformer ?f M e ^^ Suc n) {}"
      hence "(s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e) \<or> (s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer ?f M e ^^ n) {}))" by (simp add: transformer_def assms notdependshiftdown) 
       moreover {
        assume "s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e"
        hence "validfinpath M s [] s \<and> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin []) \<subseteq> A \<and> alloccurringstates s (fin []) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by simp 
      }
      moreover {
        assume "s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer ?f M e ^^ n) {})"
        then obtain s' act p s'' where "s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> act \<in> A \<and> (s, act, s') \<in> transition M \<and> validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s' (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" using IH by metis
        hence "validfinpath M s ((s, act, s')#p) s''\<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin ((s, act, s')#p)) \<subseteq> A \<and> alloccurringstates s (fin ((s, act, s')#p)) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by auto
        hence "?R s" by blast
      }
      ultimately show "?R s" by blast
    qed
  }
  ultimately show "?R s" by blast
next
  assume assum1: "?R s"
  then obtain p s' where assum1: "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by auto
  show "s \<in> \<lbrakk>mu ?f\<rbrakk> M e"
    apply (simp add: assms notdependshiftdown del: occurssimps)
    apply (rule allI)
  proof
    fix X
    assume inX : "\<lbrakk>shiftdown g 0\<rbrakk> M e \<inter> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> X}) \<subseteq> X"
    have "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<longrightarrow>
          alloccurringstates s (fin p) \<subseteq> X"
      apply (induct p arbitrary: s; rule impI)
      apply simp
      using inX apply blast
    proof-
      fix t p s
      assume IH: "\<And>s. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<longrightarrow> alloccurringstates s (fin p) \<subseteq> X"
      assume assum1: "validfinpath M s (t # p) s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin (t # p)) \<subseteq> A \<and> alloccurringstates s (fin (t # p)) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e"
      hence "validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates (target t) (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by simp
      hence alloccurringtail: "alloccurringstates (target t) (fin p) \<subseteq> X" using IH by blast
      hence "target t \<in> X \<and> action t \<in> A \<and> (source t, action t, target t) \<in> transition M \<and> source t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e" using assum1 by auto
      hence "source t \<in> X" using inX by blast
      thus "alloccurringstates s (fin (t # p)) \<subseteq> X" using alloccurringtail assum1 by simp
    qed
    thus "s \<in> X" using assum1 by simp
  qed
qed

subsection \<open>Theorem 21\<close>

lemma invariantApath : 
  assumes "S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' a. a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> S'}"
  and "s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e }"
  shows "\<exists>s' a. a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e}"
proof-
  have "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' a. a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> S')" using assms by auto
  moreover have "s \<notin> \<lbrakk>shiftdown f 0\<rbrakk> M e"
    apply (rule ccontr, simp)
  proof-
    assume "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" 
    hence "validfinpath M s [] s \<and> alloccurringactions (fin []) \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" by auto
    thus False using assms(2) by blast
  qed
  ultimately obtain a s' where assum1 : "a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> S'" by auto  
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e"
    apply (rule ccontr, simp)
  proof-
    assume "\<exists>p. action ` set p \<subseteq> A \<and> (\<exists>s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e)"
    then obtain p s'' where "validfinpath M s' p s'' \<and> action ` set p \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e " by auto
    hence "validfinpath M s ((s, a, s')#p) s'' \<and> alloccurringactions (fin ((s, a, s')#p)) \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e " using assum1 by simp
    thus False using assms(2) by blast
  qed
  thus ?thesis using assum1 by auto
qed

lemma theorem21generalized :  
  assumes "\<not>dependvar f M 0"
  and "finite A"
  shows "(s \<in> \<lbrakk>\<nu> f \<or>\<^sub>\<mu> \<langle>Acts A\<rangle>\<^sub>R var 0\<rbrakk> M e) =
  ((\<exists>p s'. validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e) \<or> 
  (\<exists>p. validinfpath M s p \<and> alloccurringactions (inf p) \<subseteq> A))"
  (is "s \<in> \<lbrakk>\<nu> ?f\<rbrakk> M e = (?R\<^sub>1 s \<or> ?R\<^sub>2 s)")
  apply (rule iffI)
  defer
  apply (simp add: assms(2) del: Diamond.simps)
  apply (subst notdependshiftdown)
  apply (simp add: assms(1))
  apply (rule exI)
proof
  assume "s \<in> \<lbrakk>nu ?f\<rbrakk> M e"
  hence "\<exists>S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(2) by (simp del: Diamond.simps)
  then obtain S' where "S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" by auto
  hence assum1 : "S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(1) notdependshiftdown by blast
  have "\<not>?R\<^sub>1 s \<Longrightarrow> (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))"
    apply (rule successorlemma)
  proof-
    assume assum2 : "\<not>?R\<^sub>1 s"
    let ?S' = "S' \<inter> {s'. \<not>?R\<^sub>1 s'}" 
    have "(\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))"
      apply (rule allI)
    proof
      fix s
      assume assum3 : "s \<in> ?S'"
      have "S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<Longrightarrow> s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> set (map action p) \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e } \<Longrightarrow> \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e}" using invariantApath by simp
      hence "\<exists>s'' act. act \<in> A \<and> (s, act, s'') \<in> (transition M) \<and> s'' \<in> ?S'" using assum1 assum3 assms(1) by simp
      thus "\<exists>t. source t = s \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S'" by auto
    qed
    moreover have "s \<in> ?S'" using assum1 assum2 by auto
    ultimately show "s \<in> ?S' \<and> (\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))" by simp
  qed
  thus "?R\<^sub>1 s \<or> ?R\<^sub>2 s" by (simp only: image_subset_iff alloccurringmap.simps; auto)
next
  let ?S' = "{s. ?R\<^sub>1 s \<or> ?R\<^sub>2 s}"
  assume "(\<exists>p s'. validfinpath M s p s' \<and> action ` set p \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e) \<or> (\<exists>p. validinfpath M s p \<and> action ` range p \<subseteq> A)"
  thus "s \<in> ?S'" by simp
  show "?S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}"
  proof
    fix s
    assume "s \<in> ?S'"
    moreover {  
      assume "?R\<^sub>1 s"
      then obtain p s' where assum1 : "validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" by auto
      have "validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<Longrightarrow> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e))"
        apply (induct p arbitrary : s; simp)
      proof-
        fix t p
        assume "t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e"
        hence "(source t, action t, target t) \<in> transition M \<and> (validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e)" using splittransition by metis
        thus "source t \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (source t, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> action ` set p \<subseteq> A \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e))" by blast
      qed
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by auto
    }
    moreover {
      assume "?R\<^sub>2 s"
      then obtain p where assum1 :"validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)" unfolding alloccurringmap.simps by blast
      hence "s = source (p 0) \<and> (p 0) \<in> transition M \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by (simp add: validinfpath_def)
      hence "(s, action (p 0), target (p 0)) \<in> transition M  \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by simp
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" unfolding alloccurringmap.simps using assum1 by blast
   }
   ultimately show "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" by blast
 qed
qed

theorem theorem21 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> [Acts (-B)]\<^sub>R ff \<or>\<^sub>\<mu> \<langle>Acts (-\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)\<rbrakk> M e 
    = (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s p)"
  apply (subst negformula)
proof-
  have "\<forall>s. s \<in> \<lbrakk>Diamond \<rho> (nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (-B)) ff)) (Diamond (Acts (-\<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e 
    = (\<exists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s p )"
    apply (subst Diamondmatch)
    apply (simp add: assms splitviolating del: formulasemantics.simps)
    apply (subst theorem21generalized; ((subst alloccursnotoccurs)+)?; simp add: assms notoccursnotdepends Boxcomplement_locked Diamond_enabled del: Diamond.simps Box.simps Diamond_eq_exist Box_eq_forall occurssimps)
  proof
    have "\<And>s'. (\<exists>p. validpath M s' p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s' p) = ((\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not>occurs \<alpha>\<^sub>f (inf p))) "
      by (subst freeuntiloccurrenceprogressing_lockedenabled; simp)
    thus "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> ((\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s'' \<alpha>\<^sub>e \<or> locked M B s'')) \<or> (\<exists>p. validinfpath M s' p \<and> \<not>occurs \<alpha>\<^sub>f (inf p)))) = (\<exists>p p' s'. validfinpath M s p s' \<and> match \<rho> p \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s' p')" by blast
  qed
  thus "(s \<notin> \<lbrakk>Diamond \<rho> (nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (-B)) ff)) (Diamond (Acts (-\<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e) = (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s p)" by blast
qed

subsection \<open>Lemma 50\<close>

lemma lemma50 : 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (\<alpha>\<^sub>_el a)"
  and "\<not>dependvar (\<phi>_off a) M 0"
  shows "s \<in> \<lbrakk>\<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<phi>_off a \<and>\<^sub>\<mu> var 0) \<or>\<^sub>\<mu> \<langle>Acts (\<alpha>\<^sub>_el a -\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)\<rbrakk> M (newenvironment e S') 
    = (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> 
        (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> ((\<alpha>\<^sub>_el a) - \<alpha>\<^sub>f) \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))"
  apply (subst Diamondmatch)
  apply (simp add: assms enabled_def)
  apply (subst matchstaract)
  apply (simp add: assms)
  apply (subst alloccursnotoccurs; subst notdependshiftdown; simp add: assms)
  apply meson
  done 

subsection \<open>Theorem 24\<close>
                                 
lemma occursactionorstate : 
  assumes "\<And>s'. (\<exists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'') \<Longrightarrow> s' \<in> S'"
  and "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<and> (occurs A (fin p) \<or> occursstate S'' s (fin p))"
  shows "\<exists>p' s'. validfinpath M s p' s' \<and> ((s' \<in> S' \<inter> S'') \<or> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> A \<and> s'' \<in> S'))"
proof-
  have "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<Longrightarrow> (\<forall>i < length p. source (p!i) \<in> S')"
    apply (rule allI)
  proof
    fix i
    assume assum1 : "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
    assume "i < length p"
    hence "validfinpath M (source (p!i)) (drop i p) s' \<and> locked M B s'" using assum1 by auto
    moreover have "\<not>occurs \<alpha>\<^sub>f (fin (drop i p))" using assum1 by (subst notoccursfinright; blast)
    ultimately show "source (p!i) \<in> S'" using assms by blast
  qed
  hence "\<forall>i < length p. source (p!i) \<in> S'" using assms by auto
  hence "set (map source p) \<subseteq> S'" using occurs_map_exists_fin subsetI by metis
  moreover have "s' \<in> S'"
  proof-
    have "validfinpath M s' [] s' \<and> \<not>occurs \<alpha>\<^sub>f (fin []) \<and> locked M B s'" using assms by auto
    thus "s' \<in> S'" using assms by metis
  qed
  ultimately have "insert s' (set (map source p)) \<subseteq> S'" by simp
  moreover have "(insert s' (set (map source p)) \<subseteq> S') = (insert s (set (map target p)) \<subseteq> S')" by (subst sourcetargetfin[of M _ _ s']; simp add: assms)
  ultimately have allstatesinS' : "s \<in> S' \<and> (\<forall>i< length p. target (p!i) \<in> S')" by (simp add: subset_iff)
  {
    assume "validfinpath M s p s' \<and> occurs A (fin p)"
    moreover from this obtain i where "i < length p \<and> action (p!i) \<in> A" using occursfinalternative by blast
    ultimately have "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M \<and> action (p!i) \<in> A \<and> target (p!i) \<in> S'" using allstatesinS' by auto
    hence "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> A \<and> s'' \<in> S')" by blast
  }
  moreover {
    assume assum1: "validfinpath M s p s' \<and> occursstate S'' s (fin p)"
    hence "s \<in> S'' \<or> (\<exists>i < length p. target (p!i) \<in> S'')" unfolding occursstatealternative by auto
    moreover have "s \<in> S'' \<Longrightarrow> validfinpath M s [] s \<and> s \<in> S' \<inter> S''"using assum1 allstatesinS' by auto
    moreover {
      assume "\<exists>i < length p. target (p!i) \<in> S''" 
      then obtain i where assum2 : "i < length p \<and> target (p!i) \<in> S''" by auto
      hence "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M" using assum1 by auto
      hence "validfinpath M s ((take i p) @ [(source (p!i), action (p!i), target (p!i))]) (target (p!i)) \<and> (target (p!i)) \<in> S''" using assum2 by simp
      hence "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" using assum2 allstatesinS' by blast
    }
    ultimately have "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" by blast
  }
  ultimately show ?thesis using assms by blast
qed

lemma feasiblesublemma :
  assumes exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e "
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  and reachable: "\<And>s T. s \<in> S' \<and> T \<in> \<T> \<Longrightarrow> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)))"
  and "finite \<T>"
  and "\<exists>T \<in> \<T>. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  shows "s \<in> S' \<Longrightarrow> \<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p))"
proof-
  assume assum1: "s \<in> S'"
  have "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p))"
    apply (induct \<T> rule: inductfiniteset)
    apply (simp add: assms)
    apply (subgoal_tac "validfinpath M s [] s \<and> \<not>occurs \<alpha>\<^sub>f (fin [])")
    using assum1 apply blast
    apply simp
  proof-
    fix T A'
    case (3 T A')
    then obtain p s' where IH : "T \<in> \<T> - A' \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T. T \<in> A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p))" by auto
    have "(s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p)) \<or> (s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el T) (fin p))" by auto
    moreover {
      assume "s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p)"
      hence "validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T'. T' \<in> insert T A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T') 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T') 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T') (fin p))" using IH by blast
    }
    moreover {
      assume "s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el T) (fin p)"
      moreover have "T \<in> \<T>" using IH by auto
      ultimately obtain p' s'' where validpath: "validfinpath M s' p' s'' \<and> s'' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> ((occurs (\<alpha>_el T) (fin p') \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s' (fin p')))" using IH persistent reachable by metis
      hence "(occurs (\<alpha>_el T) (extendfinpath p (fin p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (extendfinpath p (fin p')))" using occursleftorright IH validfinpathlaststate by metis
      moreover have "\<forall>T'. T' \<in> A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T') 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T') 0\<rbrakk> M e) s (extendfinpath p (fin p')) \<or> occurs (\<alpha>_el T') (extendfinpath p (fin p'))" using IH occursleftorright by metis
      ultimately have "validfinpath M s (p @ p') s'' \<and> s'' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p @ p')) \<and> (occurs (\<alpha>_el T) (fin (p @ p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin (p @ p'))) \<and>
        (\<forall>T'. T' \<in> A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T') 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T') 0\<rbrakk> M e) s (fin (p @ p')) \<or> occurs (\<alpha>_el T') (fin (p @ p')))" using validpath IH by auto
      hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T'. T' \<in> insert T A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T') 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T') 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T') (fin p))" by blast
    }
    ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T'. T' \<in> insert T A' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T') 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T') 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T') (fin p))" by blast
  qed
  moreover have "\<And>p. (\<forall>T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> p \<noteq> []" using assms(5) exclusive by auto
  ultimately show ?thesis by auto
qed

lemma constructfairpath :
  assumes exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e "
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el T) (fin p) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  and reachable: "\<forall>s \<in> S'. \<forall>T \<in> \<T>. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)))"
  and "finite \<T>"
  and "\<And>s. s \<in> S' \<Longrightarrow> \<exists>T \<in> \<T>. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  shows "s \<in> S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>T \<in> \<T>. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
proof-
  assume assum1: "s \<in> S'"
  have "\<forall>s \<in> S'. \<exists>p. p \<noteq> [] \<and> validfinpath M s p (laststate_nonexhaustive p) \<and> laststate_nonexhaustive p \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p))" 
  (is "\<forall>s \<in> S'. ?P s")
  proof
    fix s
    assume "s \<in> S'"
    hence "\<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el T) (fin p))" 
      apply (subst feasiblesublemma)
      using exclusive persistent reachable assms(4) assms(5) apply blast+
      done
    thus "?P s" using validfinpathlaststate laststate_laststate_nonexhaustive by metis
  qed
  then obtain succ where assum2: "\<forall>s' \<in> S'. succ s' \<noteq> [] \<and> validfinpath M s' (succ s') (laststate_nonexhaustive (succ s')) \<and> laststate_nonexhaustive (succ s') \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s')) \<and> (\<forall>T. T \<in> \<T> \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s' (fin (succ s')) \<or> occurs (\<alpha>_el T) (fin (succ s')))" by metis
  let ?p = "recursiveconcpaths succ s"
  have validinfpath: "validinfpath M s ?p" using validinfpathconc assum1 assum2 by metis
  moreover have "\<not>occurs \<alpha>\<^sub>f (inf ?p)"
    apply (subst occursinfalternative) 
    apply (subst validpredconc [of "\<lambda>s. \<lambda>p. \<not>occurs \<alpha>\<^sub>f (fin p)" _ "\<lambda>s. \<lambda>t. action (t) \<notin> \<alpha>\<^sub>f"])
    using assum1 assum2 apply auto
    done
  moreover have "\<forall>a \<in> \<T>. ((\<forall>i. (source (?p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p)))))"
    apply (rule ballI allI)+
  proof
    fix T i
    assume Tintasks: "T \<in> \<T>"
    assume phion: "source (?p i) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
    obtain j s' where assum3: "s' \<in> S' \<and> j < length (succ s') \<and> suffix i ?p = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" using suffix_recursiveconcpaths assum1 assum2 by metis
    moreover have "validinfpath M (source (?p i)) (suffix i ?p)" using validinfpath validinfsubpathright by metis
    moreover have laststate: "drop j (succ s') \<noteq> [] \<and> laststate (source (?p i)) (drop j (succ s')) = laststate_nonexhaustive (succ s')" using assum3 by (simp add: laststate_laststate_nonexhaustive)
    ultimately have "validfinpath M (source (?p i)) (drop j (succ s')) (laststate (source (?p i)) (drop j (succ s')))" using validinfpathsplitlaststate by metis
    { 
      moreover assume "\<not>occurs (\<alpha>_el T) (fin (drop j (succ s'))) \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s')))"
      ultimately have "laststate (source (?p i)) (drop j (succ s')) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e" using persistent Tintasks phion by metis
      hence "occurs (\<alpha>_el T) (fin (succ (laststate_nonexhaustive (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (laststate (source (?p i)) (drop j (succ s'))) (fin (succ (laststate_nonexhaustive (succ s'))))" using Tintasks assum2 assum3 laststate by metis
    } 
    hence "occurs (\<alpha>_el T) (extendfinpath (drop j (succ s')) (fin (succ (laststate_nonexhaustive (succ s'))))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (?p i)) (extendfinpath (drop j (succ s')) (fin (succ (laststate_nonexhaustive (succ s')))))" using occursleftorright by metis
    hence res1: "occurs (\<alpha>_el T) (fin (drop j (succ s') @ (succ (laststate_nonexhaustive (succ s'))))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s') @ (succ (laststate_nonexhaustive (succ s')))))" by simp
    have "inf (suffix i ?p) = extendfinpath (drop j (succ s')) (inf (recursiveconcpaths succ (laststate_nonexhaustive (succ s'))))" using assum3 by auto
    moreover have "succ (laststate_nonexhaustive (succ s')) \<noteq> []" using assum2 assum3 by auto    
    ultimately have "inf (suffix i ?p) = extendfinpath ((drop j (succ s')) @ (succ (laststate_nonexhaustive (succ s')))) (inf (recursiveconcpaths succ (laststate_nonexhaustive (succ (laststate_nonexhaustive (succ s'))))))" by (simp add: unfoldrecursiveconcpaths)
    thus "occurs (\<alpha>_el T) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))"  using occursleft occursstateleft res1 by metis
  qed
  ultimately show ?thesis by blast
qed

lemma infpathoccursoroccursstate : 
  assumes "validinfpath M s p \<and> (occurs A (inf p) \<or> occursstate S' s (inf p))"
  shows "\<exists>i. source (p i) \<in> S' \<or> action (p i) \<in> A" 
  using assms ind.simps(2) occursinfalternative occursstatealternative validinfpath_def by metis

lemma theorem24_subformula :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>T \<in> \<T>. finite (\<alpha>_el T)) \<and> finite \<T>"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_off T) M 0"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_on T) M 0"
  and invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> P s (inf p) =  (\<forall>T \<in> \<T>. (\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))"
  and locking: "\<And>s. locked M B s = (\<forall> T \<in> \<T>. s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e)"
  and exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el T) (fin p) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  shows "s \<in> \<lbrakk>nu (And \<T> (\<lambda>T. or (neg (\<phi>_on T)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) -\<alpha>\<^sub>f)) (var 0))))))\<rbrakk> M e
    = ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
  apply (simp add: assms del: Diamond.simps occurssimps locking)
proof 
  assume "\<exists>S'. S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')}) \<and> s \<in> S'"
  then obtain S' where "s \<in> S' \<and> (\<forall>T \<in> \<T>. S' \<subseteq> {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')})" by blast
  moreover have "\<And>T. T \<in> \<T> \<Longrightarrow> {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')} \<subseteq> {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el T -\<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))}" by (subst lemma50; (subst notdependshiftdown)?; simp; simp add: assms)
  ultimately have assum1: "S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'" by blast
  let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)}"
  have "\<forall>s \<in> ?S'. \<forall>T \<in> \<T>. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)))"
    apply (rule ballI)+
  proof
    fix s T
    assume assum2: "s \<in> ?S'"
    hence "s \<in> S'" by auto
    moreover assume "T \<in> \<T>"
    moreover assume "s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
    ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el T \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'))" using assum1 by auto
    then obtain p s' where validpath: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el T \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'))" using assum1 by presburger
    moreover have "enabled M s' \<alpha>\<^sub>e \<Longrightarrow> False" using assum2 validpath by auto
    moreover {
      assume s'inS' : "s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e"
      hence "occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)" using validpath notoccursendpath by metis
      moreover have "\<nexists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" 
      proof
        assume "\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)"
        then obtain p' s'' where "validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" by auto
        hence "validfinpath M s (p @ p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p @ p')) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" using validpath addpathsnotoccurs by metis
        thus False using assum2 by blast
      qed
      ultimately have "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)" using validpath s'inS' by auto
    }
    moreover {
      assume "\<exists>s'' a'. a' \<in> \<alpha>_el T \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'"
      then obtain a' s'' where s''inS': "a' \<in> \<alpha>_el T \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'" by auto
      hence "validfinpath M s' [(s', a', s'')] s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin ([(s', a', s'')])) \<and> occurs (\<alpha>_el T) (fin (p @ [(s', a', s'')]))" by auto
      hence validaddpath : "validfinpath M s (p @ [(s', a', s'')]) s'' \<and>  \<not>occurs \<alpha>\<^sub>f (fin (p @ [(s', a', s'')])) \<and> occurs (\<alpha>_el T) (fin (p @ [(s', a', s'')]))" using validpath validfinpathsplit addpathsnotoccurs by metis 
      moreover have "\<nexists>p s'. validfinpath M s'' p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)" 
      proof
        assume "\<exists>p s'. validfinpath M s'' p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)"
        then obtain p' s''' where "validfinpath M s'' p' s''' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s''' \<or> enabled M s''' \<alpha>\<^sub>e)" by auto
        hence "validfinpath M s ((p @ [(s', a', s'')]) @ p') s''' \<and> \<not>occurs \<alpha>\<^sub>f (fin ((p @ [(s', a', s'')]) @ p')) \<and> (locked M B s''' \<or> enabled M s''' \<alpha>\<^sub>e)" using validaddpath addpathsnotoccurs by metis
        thus False using assum2 by blast
      qed
      ultimately have "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> occurs (\<alpha>_el T) (fin p)" using s''inS' by blast
    }
    ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p))" by blast
  qed
  moreover have "\<And>s. s \<in> ?S' \<Longrightarrow> \<not>locked M B s" 
    apply (subgoal_tac "validfinpath M s [] s \<and> \<not>occurs \<alpha>\<^sub>f (fin [])")
    apply blast
    apply simp
    done
  moreover have negnegT : "-(-\<T>) = \<T>" by auto
  ultimately have "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>T \<in> -(-\<T>). ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
    apply (subst constructfairpath; (subst negnegT)?)
    using exclusive apply blast
    using persistent apply blast
    using assms(1) apply blast+
    using locking apply meson
    using persistent assms(1) apply blast+
    done
  hence "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)" using invarinf by blast
  thus "((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))" using assum1 by blast
next
  let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))}"
  assume "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))"
  hence "s \<in> ?S'" by simp
  moreover have "?S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> ?S')))})"
    apply (rule subsetI INT_I CollectI impI)+
  proof-
    fix s T
    assume assum1: "s \<in> ?S'"
    assume assum2 : "T \<in> \<T>"
    assume assum3 : "s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e" 
    show "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> ?S'))"
    proof-
      have "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))" using assum1 by auto
      moreover {
        assume "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)"
        hence "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)" by auto
        moreover {
          assume "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
          then obtain p s' where assum4: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'" by auto
          moreover have "occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)"
            apply (rule ccontr)
            apply (subgoal_tac "s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e")
            using locking persistent assum2 assum3 assum4 apply blast+
            done
          ultimately have assum4: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p))" by auto
          moreover {
            assume "occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)"
            hence "s \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists> n \<in> indicespath (fin p). target (ind n (fin p)) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e)" using occursstatealternative by metis
            hence "s \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists> n < length p. target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e)" by simp
            moreover have "s \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<Longrightarrow> validfinpath M s [] s \<and> \<not>occurs \<alpha>\<^sub>f (fin [])  \<and> s \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e" using assum1 by simp
            moreover {
              assume "\<exists> n < length p. target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e"
              then obtain n where "n < length p \<and> target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e" by auto
              hence "validfinpath M (target (p!n)) (drop (Suc n) p) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (drop (Suc n) p)) \<and> locked M B s' \<and> validfinpath M s (take (Suc n) p) (target (p!n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (take (Suc n) p)) \<and> target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e" 
                using assum4 validfinsubpathtargetright notoccursfinright occursfinleft validfinsubpathtarget by metis
              hence "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)  \<and> s' \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e" by auto
            }
            ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)  \<and> s' \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e" by blast
          }
          moreover {
            assume "occurs (\<alpha>_el T) (fin p)"
            then obtain n where "n < length p \<and> action (p!n) \<in> \<alpha>_el T" using occursfinalternative by blast
            hence "validfinpath M (target (p!n)) (drop (Suc n) p) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (drop (Suc n) p)) \<and> locked M B s' \<and> validfinpath M s (take n p) (source (p!n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (take n p)) \<and> (source (p!n), action (p!n), target (p!n)) \<in> transition M \<and> action (p!n) \<in> \<alpha>_el T \<and> action (p!n) \<notin> \<alpha>\<^sub>f" 
              using assum4 validfinsubpath validfinsubpathtargetright notoccursfinright occursfinleft occursfinalternative ithtransitionfinpath splittransition by metis
            hence "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)  \<and> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> s'' \<in> ?S')" by blast
          }
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> ((s' \<in> ?S' \<inter> (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e)) \<or> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> s'' \<in> ?S'))" 
          by meson
        }
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T \<and> a \<notin> \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> ?S'))" by blast
      }
      moreover {
        assume "\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)"
        then obtain p where predP: "validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>T \<in> \<T>. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))" using invarinf by auto
        moreover from this have "source (p 0) = s \<and> suffix 0 p = p" by (simp add: validinfpath_def)
        ultimately have validinfpath: "validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (occurs (\<alpha>_el T) (inf p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (inf p))" using assum2 assum3 by metis
        then obtain i where sourceoraction : "source (p i) \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> action (p i) \<in> \<alpha>_el T" using infpathoccursoroccursstate by metis
        have "\<And>j. source (p j) \<in> ?S'"
        proof-
          fix j
          have "validinfpath M (source (p j)) (suffix j p) \<and> \<not>occurs \<alpha>\<^sub>f (inf (suffix j p)) \<and> P (source (p j)) (inf (suffix j p))"
          proof-
            have "(\<forall>T \<in> \<T>. ((\<forall>k. (source ((suffix j p) k)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix k (suffix j p))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source ((suffix j p) k)) (inf (suffix k (suffix j p)))))))" using predP by simp
            moreover have "validinfpath M (source (p j)) (suffix j p) \<and>  \<not>occurs \<alpha>\<^sub>f (inf (suffix j p))" using predP by auto
            ultimately show ?thesis using invarinf by metis
          qed
          thus "source (p j) \<in> ?S'" by blast
        qed
        moreover have "target (p i) = source (p (Suc i))" using predP by (simp add: validinfpath_def)
        ultimately have "source (p i) \<in> ?S' \<and> target (p i) \<in> ?S'" by auto
        moreover have "validfinpath M s (prefix i p) (source (p i)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (prefix i p)) \<and> action (p i) \<notin> \<alpha>\<^sub>f" using validinfpath validinfsubpath by auto
        moreover have "(source (p i), action (p i), target (p i)) \<in> transition M" using validinfpath splittransition validinfpath_def by metis
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T \<and> a \<notin> \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> ?S'))" using sourceoraction by blast
      }
      ultimately show ?thesis by blast
    qed
  qed
  ultimately obtain S' where "S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'" by blast
  hence "s \<in> S' \<and> (\<forall>T\<in>\<T>. S' \<subseteq> {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e \<or> (\<exists>s'' a. a \<in> \<alpha>_el T - \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'" by blast
  moreover have "\<And>T. T \<in> \<T> \<Longrightarrow> {s. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el T -\<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))} \<subseteq> {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')}" by (subst lemma50; (subst notdependshiftdown)?; simp; simp add: assms)
  ultimately have "S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')}) \<and> s \<in> S'" by blast
  thus "\<exists>S'. S' \<subseteq> (\<Inter>T\<in>\<T>. {s. s \<in> \<lbrakk>\<phi>_on T\<rbrakk> M (newenvironment e S') \<longrightarrow> s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off T) (var 0))) (Diamond (Acts ((\<alpha>_el T) - \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S')}) \<and> s \<in> S'" by blast
qed

lemma predPsubpath: 
  assumes invariant: "\<And>p s. validpath M s p \<Longrightarrow> P s p = (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  shows "validpath M (target t) p \<and> t \<in> transition M \<and> P (source t) (extendfinpath [t] p) \<Longrightarrow> P (target t) p"
proof-
  assume assum1: "validpath M (target t) p \<and> t \<in> transition M \<and> P (source t) (extendfinpath [t] p)"
  hence "validpath M (source t) (extendfinpath [t] p) \<and> P (source t) (extendfinpath [t] p)" by (cases p; auto)
  hence "\<forall>T \<in> \<T>. allsuffixes (source t) (extendfinpath [t] p) (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p)" using invariant by auto
  hence "\<forall>T \<in> \<T>. allsuffixes (target t) p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p)" by auto
  thus "P (target t) p" using invariant assum1 by auto
qed

lemma predPsuperpath:
  assumes invariant: "\<And>p s. validpath M s p \<Longrightarrow> P s p = (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  shows "validpath M (target t) p \<and> t \<in> transition M \<and> P (target t) p \<Longrightarrow> P (source t) (extendfinpath [t] p)"
proof-
  assume assum1: "validpath M (target t) p \<and> t \<in> transition M \<and> P (target t) p"
  hence allsuffixes: "\<forall>T \<in> \<T>. allsuffixes (target t) p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p)" using invariant by auto
  moreover {
    fix T
    assume Tintasks: "T \<in> \<T>"
    moreover have "validfinpath M (source t) [t] (target t)" using assum1 by auto
    moreover assume "source t \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
    ultimately have "occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source t) (fin [t]) \<or> occurs (\<alpha>_el T) (fin [t]) \<or> target t \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e" using persistent by blast
    hence "occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source t) (fin [t]) \<or> occurs (\<alpha>_el T) (fin [t]) \<or> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (laststate (source t) [t]) p" using allsuffixes Tintasks unfolding allsuffixes_def by auto
    hence "occurs (\<alpha>_el T) (extendfinpath [t] p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source t) (extendfinpath [t] p)" using occursleftorright by metis
  }
  ultimately have "\<forall>T \<in> \<T>. allsuffixes (source t) (extendfinpath [t] p) (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p)" by auto
  moreover have "validpath M (source t) (extendfinpath [t] p)" using assum1 by (cases p; auto)
  ultimately show ?thesis using invariant by blast
qed

lemma predPsubpathsuperpath :
  assumes invariant: "\<And>p s. validpath M s p \<Longrightarrow> P s p = (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  shows "validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') = P s' p'"
  apply (rule P_extendpath[of M P]; simp?)
  apply (rule iffI)
  apply (rule predPsubpath[OF invariant]; simp)
  apply (rule predPsuperpath[OF invariant persistent])
  apply auto
  done
                                 
lemma feasible : 
  assumes invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> P s (inf p) =  ((\<forall>T \<in> \<T>. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and locking: "\<And>s. locked M B s = (\<forall>T \<in> \<T>. s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e)"
  and exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  and reachable: "\<And>T s. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)))"
  and "finite \<T>"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> P s (inf p))"
proof-
  let ?S' = "{s. \<nexists>p s'. validfinpath M s p s' \<and> locked M B s'}"
  have "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs {} (inf p) \<and> (\<forall>T \<in> \<T>. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
    apply (subst constructfairpath [where ?S'="?S'"])
    using exclusive persistent apply blast+
    defer
    using assms(6) apply simp
    apply simp
    using locking validfinpath.simps(1) apply metis
    apply simp
    apply simp
    apply (rule ballI impI)+
  proof-
    fix s'' T
    assume assum1: "s'' \<in> ?S'"
    assume "T \<in> \<T>"
    moreover assume "s'' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
    ultimately obtain p s' where "validfinpath M s'' p s' \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s'' (fin p))" using reachable by blast
    moreover from this have "s' \<in> ?S'" using assum1 by (subst notlocked; auto)
    ultimately show "\<exists>p s'. validfinpath M s'' p s' \<and> s' \<in> ?S' \<and> \<not>occurs {} (fin p) \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s'' (fin p))" by (simp; blast)
  qed
  hence "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> P s (inf p)" using invarinf by blast
  thus ?thesis by auto
qed

lemma invarinf :
  assumes invariant: "\<And>p s. validpath M s p \<Longrightarrow> P s p =  (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  shows "validinfpath M s p \<Longrightarrow> P s (inf p) =  ((\<forall>T \<in> \<T>. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el T) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  by (simp add: allsuffixes_validinfpath invariant)

lemma theorem24_feasible :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>T \<in> \<T>. finite (\<alpha>_el T)) \<and> finite \<T>"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_off T) M 0"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_on T) M 0"
  and invariant: "\<And>s p. validpath M s p \<Longrightarrow> P s p = (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  and locking: "\<And>s. locked M B s = (\<forall> T \<in> \<T>. s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e)"
  and exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  and feasible: "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> P s (inf p))"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<And>\<^sub>\<mu>T \<in> \<T>. \<phi>_on T \<Longrightarrow>\<^sub>R \<langle>Acts (- \<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<phi>_off T \<and>\<^sub>\<mu> var 0) \<or>\<^sub>\<mu> \<langle>Acts (\<alpha>_el T -\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p)"
  apply (subst negformula)
  apply (subst Diamondmatch)
  apply (subst theorem24_subformula; (rule invarinf[OF invariant] assms; auto)?)
  apply (subst splitviolating_predicate)
proof-
  {
    fix p
    have "\<And>s p' s'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') = P s' p'"
      by (subst predPsubpathsuperpath [where ?p=p]; (rule assms)?; auto)
  }
  hence res1: "\<And>s s' p p'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') = P s' p'" by blast
  thus "\<And>p p' s'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s' p' = P s (extendfinpath p p')" by blast  
  have "\<And>s. (\<exists>p. validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p) =
    ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
    \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
    apply (subst freeuntiloccurrenceprogressing_lockedenabled_pred[of _ B])
    apply (rule feasible)
    using res1 apply blast
    apply (subst invariant; simp add: locking exclusive)
    apply auto
    done
  thus "(\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> ((\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s' (inf p)))) =
      (\<nexists>p p' s'. validfinpath M s p s' \<and> match \<rho> p \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' p')" by blast
qed

theorem theorem24 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>T \<in> \<T>. finite (\<alpha>_el T)) \<and> finite \<T>"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_off T) M 0"
  and "\<And>T. T \<in> \<T> \<Longrightarrow> \<not>dependvar (\<phi>_on T) M 0"
  and invariant: "\<And>s p. P s p = (\<forall>T \<in> \<T>. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el T) p \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s p))" 
  and locking: "\<And>s. locked M B s = (\<forall> T \<in> \<T>. s \<notin> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e)"
  and exclusive: "\<And>s T. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' T. T \<in> \<T> \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el T) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e"
  and reachable: "\<And>T s. T \<in> \<T> \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on T) 0\<rbrakk> M e \<Longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> (occurs (\<alpha>_el T) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off T) 0\<rbrakk> M e) s (fin p)))" 
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<And>\<^sub>\<mu>T \<in> \<T>. \<phi>_on T \<Longrightarrow>\<^sub>R \<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<phi>_off T \<and>\<^sub>\<mu> var 0) \<or>\<^sub>\<mu> \<langle>Acts (\<alpha>_el T -\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p)"
  apply (rule theorem24_feasible[OF assms(1, 2, 3, 4, 5, 6, 7)]; blast?)
  apply (rule feasible[OF invarinf locking exclusive persistent]; blast?)
  using invariant reachable assms(1) apply blast+
  done

subsection \<open>Corollaries\<close>

lemma WFA_invariant: "WFA M B s p = (\<forall>a\<in> -B. allsuffixes s p (\<lambda>s p. a \<in> enabledactions M s \<longrightarrow> a \<in> alloccurringactions p \<or> occursstate {s. a \<notin> enabledactions M s} s p))"
proof-
  have "WFA M B s p = (\<forall>a \<in> -B. allsuffixes s p (\<lambda>s p. a \<in> perpetuallyenabled M s p \<longrightarrow> a \<in> alloccurringactions p))" unfolding WFA_def allsuffixes_def by auto
  moreover have "\<And>a s p. (a \<in> perpetuallyenabled M s p \<longrightarrow> a \<in> alloccurringactions p) = (a \<in> enabledactions M s \<longrightarrow> a \<in> alloccurringactions p \<or> occursstate {s. a \<notin> enabledactions M s} s p)" by (auto simp: perpetuallyenabled_def occursstate_def)
  ultimately show ?thesis by simp
qed

corollary corollary25 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<And>\<^sub>\<mu>a\<in>- B. \<langle>a\<rangle>\<^sub>\<mu>tt \<Longrightarrow>\<^sub>R \<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> ([a]\<^sub>\<mu>ff \<and>\<^sub>\<mu> var 0) \<or>\<^sub>\<mu> \<langle>Acts ({a} -\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> WFA M B s p)"
  apply (rule theorem24)
  apply (simp add: assms notoccursnotdepends)+
  apply (simp add: WFA_invariant occurs_def)
  apply (simp add: locked_def; blast)
  apply simp
proof-
  fix a s
  assume "a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e"
  then obtain s' where "(s, a, s') \<in> transition M" by auto
  hence "validfinpath M s [(s, a, s')] s' \<and> occurs {a} (fin [(s, a, s')])" by auto
  thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a} (fin p) \<or> occursstate (\<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e) s (fin p))" by blast
next
  fix s p s' a
  assume "a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs {a} (fin p)"
  hence "s' \<notin> \<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e" using notoccursendpath by metis
  thus "s' \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e" by simp
qed

lemma lockedphion_WHFA: "finite (-B) \<Longrightarrow> locked M B s = (\<forall>a\<in> -B. s \<notin> \<lbrakk>\<langle>Acts (-B)\<^sup>\<star>\<rangle>\<^sub>R \<langle>a\<rangle>\<^sub>\<mu> tt\<rbrakk> M e)"
  apply (simp only: Diamondreachable)
proof-
  have "locked M B s = WHFA M B s (fin [])" by (simp only: WHFAempty)
  thus "locked M B s = (\<forall>a\<in>-B. a \<notin> reachableactions M B s)" by (auto simp: WHFA_def perpetuallyreachable_def)
qed

lemma WHFA_invariant: "finite (-B) \<Longrightarrow> WHFA M B s p = (\<forall>a\<in>-B. allsuffixes s p (\<lambda>s p. s \<in> \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e \<longrightarrow> occurs {a} p \<or> occursstate (\<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e) s p))"
  apply (simp only: Diamondreachable)
  using Boxnotreachable
proof-
  assume assum1: "finite (-B)"
  hence "\<And>s' a.  s'\<in> \<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e =  (a \<notin> reachableactions M B s')" by (simp only: Boxnotreachable)
  hence occursnotreachable: "\<And>a s p. occursstate (\<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e) s p = (occursstate {s. a \<notin> reachableactions M B s} s p)" unfolding occursstate_def by blast
  have "WHFA M B s p = (\<forall>a \<in> -B. allsuffixes s p (\<lambda>s p. a \<in> perpetuallyreachable M B s p \<longrightarrow> a \<in> alloccurringactions p))" unfolding WHFA_def allsuffixes_def by auto
  moreover have "\<And>a s p. (a \<in> perpetuallyreachable M B s p \<longrightarrow> a \<in> alloccurringactions p) = (a \<in> reachableactions M B s \<longrightarrow> occurs {a} p \<or> occursstate {s. a \<notin> reachableactions M B s} s p)" by (auto simp: occurs_def perpetuallyreachable_def occursstate_def)
  ultimately have "WHFA M B s p = (\<forall>a\<in>-B. allsuffixes s p (\<lambda>s p. a \<in> reachableactions M B s \<longrightarrow> occurs {a} p \<or> occursstate {s. a \<notin> reachableactions M B s} s p))" by simp
  thus "WHFA M B s p = (\<forall>a\<in>-B. allsuffixes s p (\<lambda>s p. a \<in> reachableactions M B s \<longrightarrow> occurs {a} p \<or> occursstate (\<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e) s p))" apply (subst occursnotreachable) by simp
qed

corollary corollary26 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<And>\<^sub>\<mu>a\<in>-B. \<langle>Acts (-B)\<^sup>\<star>\<rangle>\<^sub>R \<langle>a\<rangle>\<^sub>\<mu>tt \<Longrightarrow>\<^sub>R \<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> ([Acts (-B)\<^sup>\<star>]\<^sub>R [a]\<^sub>\<mu>ff \<and>\<^sub>\<mu> var 0) \<or>\<^sub>\<mu> \<langle>Acts ({a} -\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> WHFA M B s p)"
  apply (rule theorem24; (simp only: shiftdownDiamond shiftdownBox shiftdown.simps)?; (rule WHFA_invariant lockedphion_WHFA)?)
  apply (simp add: assms notoccursnotdepends del: Diamond.simps Box.simps)+  using Boxnotreachable Diamondreachable assms apply meson
proof-
  fix s p s' a
  assume "a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e) s (fin p) \<and> \<not>occurs {a} (fin p)"
  hence "s' \<notin> \<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e" using notoccursendpath by meson
  hence "s' \<in> \<lbrakk>neg (Box (Star (Acts (-B))) (box a ff))\<rbrakk> M e" by simp
  moreover have "\<lbrakk>neg (box a ff)\<rbrakk> M e = \<lbrakk>diamond a tt\<rbrakk> M e" by auto
  ultimately show "s' \<in> \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e" using negBox Diamond_eq by metis
next
  fix a s
  assume "a \<in> - B \<and> s \<in> \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e"
  hence "a \<in> reachableactions M B s" by (simp only: Diamondreachable assms)
  then obtain p s' s'' where "validfinpath M s p s' \<and> (s', a, s'') \<in> transition M" by (auto simp: reachableactionsdef)
  hence "validfinpath M s (p@[(s', a, s'')]) s'' \<and> occurs {a} (fin (p@[(s', a, s'')]))" by simp
  thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a} (fin p) \<or> occursstate (\<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e) s (fin p))" by blast
qed

lemma JA_invariant:
"JA M con B s p = (\<forall>a\<in>-B. allsuffixes s p (\<lambda>s p. a \<in> enabledactions M s \<longrightarrow> occurs {a'. \<not>con a a'} p))"
  unfolding JA_def occurs_def allsuffixes_def by blast

corollary corollary27 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B) \<and> (\<forall>a \<in> -B. finite {a'. \<not>con a a'})"
  and "concurrency M con"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho>\<rangle>\<^sub>R (\<nu> \<And>\<^sub>\<mu>a\<in>- B. \<langle>a\<rangle>\<^sub>\<mu>tt \<Longrightarrow>\<^sub>R \<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> \<langle>Acts ({a'. \<not>con a a'} - \<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> JA M con B s p)"
proof-
  have "\<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Diamond (Acts ({a'. \<not> con a a'} -\<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
    \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' ff (var 0))) (Diamond (Acts ({a'. \<not> con a a'} -\<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e"
    by (simp add: assms(1) Diamond_eq)
  moreover have "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' ff (var 0))) (Diamond (Acts ({a'. \<not> con a a'} -\<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> JA M con B s p)"
    apply (rule theorem24)
    apply (simp add: assms notoccursnotdepends)+
    apply (simp add: occursstate_def JA_invariant)
    apply (simp add: locked_def; blast)
    apply simp
  proof-
    fix a s
    assume "a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e"
    then obtain s' where "(s, a, s') \<in> transition M" by auto
    moreover have "\<not>con a a" using assms(2) by (simp add: concurrency_def irreflp_def)
    ultimately have "validfinpath M s [(s, a, s')] s' \<and> occurs {a'. \<not>con a a'} (fin [(s, a, s')])" by auto
    thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a'. \<not>con a a'} (fin p) \<or> occursstate (\<lbrakk>shiftdown ff 0\<rbrakk> M e) s (fin p))" by blast
  next
    fix s p s' a
    have "validfinpath M s p s' \<longrightarrow> enabledactions M s \<inter> preimagerelation con (alloccurringactions (fin p)) \<subseteq> enabledactions M s'" using assms(2) by (auto simp: concurrency_def)
    moreover assume "a \<in> - B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e \<and> \<not>occursstate (\<lbrakk>shiftdown ff 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs {a'. \<not>con a a'} (fin p)"
    ultimately have "a \<in> enabledactions M s'" by auto
    thus "s' \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e" by simp
  qed
  ultimately show ?thesis by blast
qed

subsection \<open>Theorems \<open>SFA\<close> and \<open>SHFA\<close>\<close>

lemma freeenabledpath : 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e"
  shows "s \<in> \<lbrakk>\<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> f)\<rbrakk> M e =
    (s \<in> \<lbrakk>\<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R f\<rbrakk> M e \<or> 
       (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e))" 
  apply (subst Diamondor)
proof-
  have "s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) (Diamond (Acts \<alpha>\<^sub>e) tt)\<rbrakk> M e = 
    (\<exists>p s'. validfinpath M s p s' \<and> match (Star (Acts (- \<alpha>\<^sub>f))) p \<and> s' \<in> \<lbrakk>Diamond (Acts \<alpha>\<^sub>e) tt\<rbrakk> M e)" by (rule Diamondmatch)
  moreover have "... = (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)" by (subst Diamond_enabled; (subst matchstaract)?; auto simp: assms)
  ultimately show "(s \<in> \<lbrakk>or (Diamond (Star (Acts (- \<alpha>\<^sub>f))) (Diamond (Acts \<alpha>\<^sub>e) tt)) (Diamond (Star (Acts (- \<alpha>\<^sub>f))) f)\<rbrakk> M e) = 
    (s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) f\<rbrakk> M e \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e))" unfolding formulasemantics.simps by blast
qed

lemma musubformula:
  fixes M :: "('a, 's) lts"
  assumes "finite (-\<alpha>\<^sub>f) "
  and "finite (UNIV :: 's set)"
  shows "s \<in> \<lbrakk>\<mu> var (Suc 0) \<and>\<^sub>\<mu> (\<langle>a\<rangle>\<^sub>\<mu>var (Suc 0) \<or>\<^sub>\<mu> \<langle>Acts (-\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)\<rbrakk> M e =
  (\<exists>p s' s''. validfinpath M s p s' \<and> alloccurringstates s (fin p) \<subseteq> e 0 \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> e 0)"
  by (subst proposition40; (rule notoccursnotdepends)?; simp add: assms; auto; blast)

lemma alwaysnextaction_pred: "validinfpath M s p \<and> a \<in> {a. allsuffixes s (inf p) (\<lambda>s p. \<exists>s \<in> alloccurringstates s p. Q s a)} \<Longrightarrow>\<exists>n>m. Q (source (p n)) a"
proof-
  fix m
  assume assum1: "validinfpath M s p \<and> a \<in> {a. allsuffixes s (inf p) (\<lambda>s p. \<exists>s \<in> alloccurringstates s p. Q s a)}"
  hence "\<exists>s \<in> insert (target (p m)) {target (p (Suc m + i)) | i. True}. Q s a" by (auto simp: allsuffixes_def)
  hence "\<exists>s \<in> {target (p i) | i. i \<ge> m}. Q s a" using nat_le_iff_add Suc_leD by blast
  then obtain n where "n \<ge> m \<and> Q (target (p n)) a" by auto
  hence "Suc n > m \<and> Q (source (p (Suc n))) a" using assum1 by (simp add: validinfpath_def)
  thus "\<exists>n>m. Q (source (p n)) a" by blast
qed

lemma relentlessly_subpath': 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "validinfpath M s p  \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> alloccurringstates s (inf p) \<subseteq> X \<and> a \<in> A s (inf p)"
  shows "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> Q a s'"
proof-
  have "\<exists>n>0. Q a (source (p n))" using assms by (subst alwaysnextaction_pred; auto) 
  then obtain n where "Q a (source (p n))" by auto
  moreover have "validfinpath M s (prefix n p) (source (p n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (prefix n p)) \<and> alloccurringstates s (fin (prefix n p)) \<subseteq> X " using assms by auto
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> Q a s'" by blast
qed

lemma notreachable_validpath: "validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<notin> reachableactions M B s \<Longrightarrow> a \<notin> reachableactions M B s'"
proof-
  assume assum1: "validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<notin> reachableactions M B s"
  hence "validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> s \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'}" by (simp add: reachableactions_def reachableactionsset_def)
  hence "s' \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'}" by (subst notlockedoccurs[of s M B _ p]; simp)
  thus ?thesis by (simp add: reachableactions_def reachableactionsset_def)
qed

lemma P_feasible :
  assumes "finite (-B)"
  and "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s" 
  and "\<And>s. (\<forall>a \<in> -B. \<not>Q a s) \<Longrightarrow> locked M B s"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> P s (inf p))"
proof-
  let ?S' = "{s. \<nexists>p s'. validfinpath M s p s' \<and> locked M B s'}"
  have "\<And>s. s \<in> ?S' \<Longrightarrow> (\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin p) \<or> a \<notin> reachableactions M {} s'))"
    apply (rule inductfiniteset[where ?A="-B"])
    using assms apply simp
  proof-
    fix s
    assume "s \<in> ?S'"
    moreover have "validfinpath M s [] s \<and> (\<forall>a \<in> {}. a \<in> alloccurringactions (fin []) \<or> a \<notin> reachableactions M {} s)" by auto
    ultimately show "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a \<in> {}. a \<in> alloccurringactions (fin p) \<or> a \<notin> reachableactions M {} s')" by blast
  next
    fix s a A'
    assume "s \<in> ?S'"
    assume "a \<in> - B - A' \<and> (\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a\<in>A'. a \<in> alloccurringactions (fin p) \<or> a \<notin> reachableactions M {} s'))"
    then obtain p s' where IH: "a \<in> - B - A' \<and> s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a'\<in>A'. a' \<in> alloccurringactions (fin p) \<or> a' \<notin> reachableactions M {} s')" by auto
    have "a \<in> reachableactions M {} s' \<or> a \<notin> reachableactions M {} s'" by auto
    moreover {
      assume "a \<in> reachableactions M {} s'"
      then obtain p' s'' s''' where "validfinpath M s' p' s'' \<and> (s'', a, s''') \<in> transition M" unfolding reachableactions_def reachableactionsset_def enabledactions_def by blast 
      hence validpath: "validfinpath M s' (p'@[(s'', a, s''')]) s'''" by auto
      have "\<And>a'. a' \<in> alloccurringactions (fin p) \<Longrightarrow> a' \<in> alloccurringactions (fin (p@p'@[(s'', a, s''')]))" by auto
      moreover have "\<And>a'.  a' \<notin> reachableactions M {} s' \<Longrightarrow>  a' \<notin> reachableactions M {} s'''" using validpath notreachable_validpath notoccursempty by metis
      moreover have "a \<in> alloccurringactions (fin (p@p'@[(s'', a, s''')]))" by auto
      ultimately have "\<forall>a'\<in>insert a A'. a' \<in> alloccurringactions (fin (p@p'@[(s'', a, s''')])) \<or> a' \<notin> reachableactions M {} s'''" using IH by blast
      moreover have "s' \<in> ?S' \<Longrightarrow> s''' \<in> ?S'" apply (rule notlocked) using validpath by blast
      ultimately have "s''' \<in> ?S' \<and> validfinpath M s (p@p'@[(s'', a, s''')]) s''' \<and> (\<forall>a'\<in>insert a A'. a' \<in> alloccurringactions (fin (p@p'@[(s'', a, s''')])) \<or> a' \<notin> reachableactions M {} s''')" using IH validpath by auto
      hence "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a'\<in>insert a A'. a' \<in> alloccurringactions (fin p) \<or> a' \<notin> reachableactions M {} s')" by blast
    }
    moreover {
      assume "a \<notin> reachableactions M {} s'"
      hence "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a'\<in>insert a A'. a' \<in> alloccurringactions (fin p) \<or> a' \<notin> reachableactions M {} s')" using IH by blast
    }
    ultimately show "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> (\<forall>a'\<in>insert a A'. a' \<in> alloccurringactions (fin p) \<or> a' \<notin> reachableactions M {} s')" by blast
  qed
  hence "\<forall>s. \<exists>succ. s \<in> ?S' \<longrightarrow> (\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s succ s' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin succ) \<or> a \<notin> reachableactions M {} s'))" by meson
  hence "\<exists>succ. \<forall>s \<in> ?S'. \<exists>p s'. s' \<in> ?S' \<and> validfinpath M s (succ s) s' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> a \<notin> reachableactions M {} s')" by (rule succswitch)
  then obtain succ where succ : "\<forall>s \<in> ?S'. \<exists>p s'. s' \<in> ?S' \<and> validfinpath M s (succ s) s' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> a \<notin> reachableactions M {} s')" by auto
  have notempty: "\<And>s. s \<in> ?S' \<Longrightarrow> succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> ?S'"
  proof
    fix s
    assume inS': "s \<in> ?S'"
    then obtain s' where assum1: "s' \<in> ?S' \<and> validfinpath M s (succ s) s' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> a \<notin> reachableactions M {} s')" using succ by meson
    show "succ s \<noteq> []"
    proof
      assume emptypath: "succ s = []"
      have "\<forall>a \<in> -B. a \<notin> enabledactions M s'"
      proof
        fix a
        have "a \<notin> alloccurringactions (fin (succ s))" using emptypath by simp
        moreover assume "a \<in> -B"
        ultimately have "a \<notin> reachableactions M {} s'" using assum1 by blast
        thus "a \<notin> enabledactions M s'" using enabled_reachable in_mono by metis     
      qed
      hence "validfinpath M s' [] s' \<and> locked M B s'" by (auto simp: locked_def)
      thus False using assum1 by blast
    qed
    hence "s' = laststate_nonexhaustive (succ s)" using assum1 validfinpathlaststate laststate_laststate_nonexhaustive by metis
    thus "laststate_nonexhaustive (succ s) \<in> ?S'" using assum1 by auto
  qed
  have validpath: "\<And>s. s \<in> ?S' \<Longrightarrow> validinfpath M s (recursiveconcpaths succ s)"
    apply (rule validinfpathconc[where ?S'="?S'"]; rule conjI)
    apply simp
    using notempty succ apply meson
    done
  have "\<And>s. s\<in>?S' \<Longrightarrow> P s (inf (recursiveconcpaths succ s))" apply (rule P_alternative[OF assms(4, 5)])
  proof-
    fix s n a
    assume inS': "s\<in>?S'"
    assume inBcomp: "a \<in> A (target (recursiveconcpaths succ s n)) (inf (suffix (Suc n) (recursiveconcpaths succ s))) -B"
    hence "\<exists>s' p. s' \<in> ?S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')" 
      apply (subst suffix_recursiveconcpathsrelentlessly[OF assms(4)]) 
      apply (rule conjI)
      using inS' apply blast
      apply (rule conjI)
      using notempty succ apply meson
      apply simp+
      done
    then obtain p s' where subpath: "s' \<in> ?S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')" by blast
    obtain s'' where subsubpath: "s'' \<in> ?S' \<and> validfinpath M s' (succ s') s'' \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s')) \<or> a \<notin> reachableactions M {} s'')" using succ subpath by meson
    moreover from this have laststate: "s'' = laststate s' (succ s')" using validfinpathlaststate by metis
    ultimately have "a \<in> alloccurringactions (fin (succ s')) \<or> a \<notin> reachableactions M {} s''" using inBcomp by blast
    moreover have unfoldrecursive: "recursiveconcpaths succ s' = conc (succ s') (recursiveconcpaths succ (laststate s' (succ s')))" using subpath by (simp add: laststate_laststate_nonexhaustive notempty unfoldrecursiveconcpaths) 
    moreover {
      have "A s' (inf (conc (succ s') (recursiveconcpaths succ (laststate s' (succ s'))))) = A s'' (inf (recursiveconcpaths succ (laststate s' (succ s'))))" by (rule relentlessly_infextendpath[OF assms(4)])
      hence "a \<in> A s'' (inf (recursiveconcpaths succ (laststate s' (succ s'))))" using subpath unfoldrecursive by simp
      hence "\<exists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs {} (fin p') \<and> alloccurringstates s'' (fin p') \<subseteq> UNIV \<and> Q a s'''"
        apply (subst relentlessly_subpath'[of A Q M _ "recursiveconcpaths succ (laststate s' (succ s'))"]; simp only: occurs_def)
        apply (simp add: assms)
        using laststate validpath subsubpath apply blast
        done
      hence "\<exists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs {} (fin p') \<and> a \<in> reachableactions M B s'''" using inBcomp assms(2) by auto
      moreover have "\<And>a s. reachableactions M B s \<subseteq> reachableactions M {} s" unfolding reachableactions_def by (rule reachableactionssubset, simp)
      ultimately have "\<exists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs {} (fin p') \<and> a \<in> reachableactions M {} s'''" by blast
      hence "a \<in> reachableactions M {}  s''" using notreachable_validpath by metis
    }
    ultimately have "a \<in> alloccurringactions (fin (succ s'))" by blast
    hence "occurs {a} (extendfinpath p (extendfinpath (succ s') (inf (recursiveconcpaths succ (laststate s' (succ s'))))))" by (subst occursright; (subst occursleft)?; simp)
    hence "a \<in> alloccurringactions (inf (conc p (conc (succ s') (recursiveconcpaths succ (laststate s' (succ s'))))))" unfolding extendfinpath.simps occurs_def by blast
    thus "a \<in> alloccurringactions (inf (suffix (Suc n) (recursiveconcpaths succ s)))" using subpath unfoldrecursive by metis
  qed
  hence "\<And>s. s \<in> ?S' \<Longrightarrow> validinfpath M s (recursiveconcpaths succ s) \<and> P s (inf (recursiveconcpaths succ s))" using validpath by auto
  thus ?thesis by blast
qed

lemma Psubformula :
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "finite (-\<alpha>\<^sub>f) \<and> finite (-B)"
  and "\<And>a. \<not>dependvar (\<phi>_on a) M 0"
  and "\<not>dependvar \<phi>_off M 0"
  and "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s" 
  and "\<And>s. (\<forall>a \<in> -B. \<not>Q a s) \<Longrightarrow> locked M B s"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  and "\<And>s a. a \<in> -B \<Longrightarrow> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e = Q a s"
  and "\<And>s. s \<in> \<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e = (\<forall>a \<in> \<alpha>\<^sub>f -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e)"
  shows "s \<in> \<lbrakk>\<langle>Acts (-\<alpha>\<^sub>f)\<^sup>\<star>\<rangle>\<^sub>R (\<nu> \<phi>_off \<and>\<^sub>\<mu> (\<And>\<^sub>\<mu>a\<in>- B. \<phi>_on a \<Longrightarrow>\<^sub>R (\<mu> var 1 \<and>\<^sub>\<mu> (\<langle>a\<rangle>\<^sub>\<mu>var 1 \<or>\<^sub>\<mu> \<langle>Acts (- \<alpha>\<^sub>f)\<rangle>\<^sub>R var 0))))\<rbrakk> M e =
        ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')
        \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
  apply (simp add: assms Diamondmatch matchstaract musubformula And_eq_all Diamondreachable notdependshiftdown del: Diamond.simps Box.simps alloccurringmap.simps And_eq_all' occurssimps formulasemantics.simps(10) assms(8))
  apply (subst alloccursnotoccurs)
  apply (subst double_complement)
  apply (rule iffI impI)+
proof-
  assume "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>X\<subseteq>\<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e. X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> X \<and> alloccurringmap target (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X)"
  then obtain p s' X where assum1: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> X \<subseteq> \<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e \<and> X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> alloccurringstates s (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X" by auto
  let ?S' = "X \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s''}"
  have "s' \<in> ?S' \<or> s' \<notin> ?S'" by auto
  moreover {
    assume assum2: "s' \<in> ?S'"
    have "\<And>s. s \<in> ?S' \<Longrightarrow> (\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')))"
      apply (rule inductfiniteset[where ?A="-B"])
      using assms apply simp
    proof-
      fix s 
      assume "s \<in> ?S'" 
      hence "s \<in> ?S' \<and> validfinpath M s [] s \<and> \<not>occurs \<alpha>\<^sub>f (fin []) \<and> alloccurringstates s (fin []) \<subseteq> X" by simp
      thus "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> {}. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" by blast
    next
      fix s a A'
      assume assum3: "s \<in> ?S'"
      assume "a \<in> - B - A' \<and> (\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a\<in>A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')))"
      then obtain p s' where IH : "a \<in> - B - A' \<and> s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a\<in>A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" by auto
      have "(\<exists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'') \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p')  \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')" by blast
      moreover {
        assume "\<exists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''"
        then obtain p' s'' where firstpath: "validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and>  Q a s''" by auto
        hence "s'' \<in> alloccurringstates s' (fin p')" using laststateoccurs by metis
        hence enabledaction: "a \<in> -B \<and> s'' \<in> X \<and>  Q a s''" using firstpath IH by auto
        then obtain p'' s''' s'''' where "validfinpath M s'' p'' s''' \<and> alloccurringstates s'' (fin p'') \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p'') \<and> (s''', a, s'''') \<in> transition M \<and> s'''' \<in> X" using assum1 by blast
        moreover have "a \<in> -\<alpha>\<^sub>f" using assum1 enabledaction assms(9) assms(10) by auto
        ultimately have secondpath: "validfinpath M s'' (p''@[(s''', a, s'''')]) s'''' \<and> alloccurringstates s'' (fin (p''@[(s''', a, s'''')])) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin (p''@[(s''', a, s'''')]))" by auto
        hence validpath: "validfinpath M s' (p'@p''@[(s''', a, s'''')]) s'''' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p'@p''@[(s''', a, s'''')])) \<and> alloccurringstates s' (fin (p'@p''@[(s''', a, s'''')])) \<subseteq> X \<and> a \<in> alloccurringactions (fin (p'@p''@[(s''', a, s'''')]))" using firstpath secondpath by auto
        hence "validfinpath M s (p@p'@p''@[(s''', a, s'''')]) s'''' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p@p'@p''@[(s''', a, s'''')])) \<and> alloccurringstates s (fin (p@p'@p''@[(s''', a, s'''')])) \<subseteq> X \<and> a \<in> alloccurringactions (fin (p@p'@p''@[(s''', a, s'''')]))" using IH by auto
        moreover have "\<forall>a' \<in> A'. a' \<in> alloccurringactions (fin (p@p'@p''@[(s''', a, s'''')])) \<or> (\<nexists>p' s''. validfinpath M s'''' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s'''' (fin p') \<subseteq> X \<and> Q a' s'')"
        proof
          fix a' 
          assume "a' \<in> A'"
          hence "a' \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a' s'')" using IH by blast
          moreover have "a' \<in> alloccurringactions (fin p) \<Longrightarrow> a' \<in> alloccurringactions (fin (p@p'@p''@[(s''', a, s'''')]))" by auto
          moreover { 
            assume assum1: "\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a' s''"
            have "\<nexists>p' s''. validfinpath M s'''' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s'''' (fin p') \<subseteq> X \<and> Q a' s''"
            proof (rule ccontr)
              assume "\<not>(\<nexists>p' s''. validfinpath M s'''' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s'''' (fin p') \<subseteq> X \<and> Q a' s'')"
              then obtain p''' s where "validfinpath M s'''' p''' s \<and> \<not>occurs \<alpha>\<^sub>f (fin p''') \<and>  alloccurringstates s'''' (fin p''') \<subseteq> X \<and> Q a' s" by blast
              hence "validfinpath M s' (p'@p''@[(s''', a, s'''')]@p''') s \<and> \<not>occurs \<alpha>\<^sub>f (fin (p'@p''@[(s''', a, s'''')]@p''')) \<and> alloccurringstates s' (fin (p'@p''@[(s''', a, s'''')]@p''')) \<subseteq> X \<and> Q a' s" using validpath by auto
              thus False using assum1 by blast
            qed
          }
          ultimately show "a' \<in> alloccurringactions (fin (p@p'@p''@[(s''', a, s'''')])) \<or> (\<nexists>p' s''. validfinpath M s'''' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s'''' (fin p') \<subseteq> X \<and> Q a' s'')" by blast
        qed
        ultimately have validfinalpath: "validfinpath M s (p@p'@p''@[(s''', a, s'''')]) s'''' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p@p'@p''@[(s''', a, s'''')])) \<and> alloccurringstates s (fin (p@p'@p''@[(s''', a, s'''')])) \<subseteq> X \<and> (\<forall>a' \<in> insert a A'. a' \<in> alloccurringactions (fin (p@p'@p''@[(s''', a, s'''')])) \<or> (\<nexists>p' s''. validfinpath M s'''' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s'''' (fin p') \<subseteq> X \<and> Q a' s''))" by simp
        moreover {
          from this have "alloccurringstates s (fin (p@p'@p''@[(s''', a, s'''')])) \<subseteq> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s''}" apply (subst allnextstatesnotlocked) using assum3 by auto
          moreover have "s'''' \<in> alloccurringstates s (fin (p@p'@p''@[(s''', a, s'''')]))" using validfinalpath laststateoccurs by metis
          ultimately have "s'''' \<in> ?S'" using validfinalpath by simp
        }
        ultimately have "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> insert a A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" by meson
      }
      moreover {
        assume "\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''"
        moreover have "\<forall>a \<in> A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')" using IH by blast
        ultimately have "s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> insert a A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" using IH by auto
        hence "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> insert a A'. a \<in> alloccurringactions  (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" by meson
      }
      ultimately show "\<exists>p s'. s' \<in> ?S' \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X \<and> (\<forall>a \<in> insert a A'. a \<in> alloccurringactions (fin p) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and>  alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" by blast
    qed
    hence "\<forall>s. \<exists>succ. s \<in> ?S' \<longrightarrow> (\<exists>s' \<in> ?S'. validfinpath M s succ s' \<and> \<not>occurs \<alpha>\<^sub>f (fin succ) \<and> alloccurringstates s (fin succ) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin succ) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')))" by meson
    hence "\<exists>succ. \<forall>s \<in> ?S'. (\<exists>s' \<in> ?S'. validfinpath M s (succ s) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s)) \<and> alloccurringstates s (fin (succ s)) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')))" by (rule succswitch)
    then obtain succ where succ: "\<forall>s \<in> ?S'. (\<exists>s' \<in> ?S'. validfinpath M s (succ s) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s)) \<and> alloccurringstates s (fin (succ s)) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s'')))" by auto
    have notempty: "\<And>s. s \<in> ?S' \<Longrightarrow> succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> ?S'"
    proof
      fix s
      assume inS': "s \<in> ?S'"
      then obtain s' where assum1: "s' \<in> ?S' \<and> validfinpath M s (succ s) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s)) \<and> alloccurringstates s (fin (succ s)) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s)) \<or> (\<nexists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<and> Q a s''))" using succ by meson
      show "succ s \<noteq> []"
      proof
        assume emptypath: "succ s = []"
        have "\<forall>a \<in> -B. \<not>Q a s'"
        proof
          fix a
          have "a \<notin> alloccurringactions (fin (succ s))" using emptypath by simp
          moreover assume "a \<in> -B"
          ultimately have notreachable: "\<And>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s' (fin p') \<subseteq> X \<Longrightarrow> \<not>Q a s''" using assum1 by blast
          thus "\<not>Q a s'" using assum1 by (subst notreachable[where ?p'="[]" and ?s''="s'"]; auto)
        qed
        hence "validfinpath M s' [] s' \<and> \<not>occurs \<alpha>\<^sub>f (fin []) \<and> locked M B s'" by (auto simp: assms(6))
        thus False using assum1 by blast
      qed
      hence "s' = laststate_nonexhaustive (succ s)" using assum1 laststate_laststate_nonexhaustive validfinpathlaststate by metis
      thus "laststate_nonexhaustive (succ s) \<in> ?S'" using assum1 by auto
    qed
    let ?p="recursiveconcpaths succ s'"
    have validpath: "\<And>s. s \<in> ?S' \<Longrightarrow> validinfpath M s (recursiveconcpaths succ s)"
      apply (rule validinfpathconc[where ?S'="?S'"]; rule conjI)
      apply simp
      using notempty succ apply meson
      done
    have "\<And>s. s \<in> ?S' \<Longrightarrow> \<forall>n. action (recursiveconcpaths succ s n) \<notin> \<alpha>\<^sub>f \<and> target (recursiveconcpaths succ s n) \<in> X"
      apply (rule validpredconc [where ?S'="?S'" and ?Q="\<lambda>s p. \<not>occurs \<alpha>\<^sub>f (fin p) \<and> alloccurringstates s (fin p) \<subseteq> X"])
      apply simp
      apply auto[1]
      using notempty succ apply meson
      done
    hence alphaffreeandX: "\<And>s. s \<in> ?S' \<Longrightarrow> \<not>occurs \<alpha>\<^sub>f (inf (recursiveconcpaths succ s)) \<and> alloccurringstates s (inf (recursiveconcpaths succ s)) \<subseteq> X" unfolding occursinfalternative by (subst alloccurringstatesinset; auto)
    have "\<And>s. s\<in>?S' \<Longrightarrow> P s (inf (recursiveconcpaths succ s))" 
      apply (rule P_alternative [of A Q])
      apply (simp add: assms)
      apply (simp add: assms)
    proof-
      fix s n a
      assume inS': "s\<in>?S'"
      assume inBcomp: "a \<in> A (target (recursiveconcpaths succ s n)) (inf (suffix (Suc n) (recursiveconcpaths succ s))) -B"
      hence "\<exists>s' p. s' \<in> ?S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')" 
        apply (subst suffix_recursiveconcpathsrelentlessly[OF assms(7)]) 
        apply (rule conjI)
        using inS' apply blast
        apply (rule conjI)
        using notempty succ apply meson
        apply simp+
        done
      then obtain p s' where subpath: "s' \<in> ?S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')" by blast
      obtain s'' where subsubpath: "s'' \<in> ?S' \<and> validfinpath M s' (succ s') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s')) \<and> alloccurringstates s' (fin (succ s')) \<subseteq> X \<and> (\<forall>a \<in> -B. a \<in> alloccurringactions (fin (succ s')) \<or> (\<nexists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s'' (fin p') \<subseteq> X \<and> Q a s'''))" using succ subpath by meson
      moreover from this have laststate: "s'' = laststate s' (succ s')" using validfinpathlaststate by metis
      ultimately have "a \<in> alloccurringactions (fin (succ s')) \<or> (\<nexists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s'' (fin p') \<subseteq> X \<and> Q a s''')" using inBcomp by blast
      moreover have unfoldrecursive: "recursiveconcpaths succ s' = conc (succ s') (recursiveconcpaths succ (laststate s' (succ s')))" using subpath by (simp add: laststate_laststate_nonexhaustive notempty unfoldrecursiveconcpaths) 
      moreover {
        have "A s' (inf (conc (succ s') (recursiveconcpaths succ (laststate s' (succ s'))))) = A s'' (inf (recursiveconcpaths succ (laststate s' (succ s'))))" by (rule relentlessly_infextendpath[OF assms(7)])
        hence "a \<in> A s'' (inf (recursiveconcpaths succ (laststate s' (succ s'))))" using subpath unfoldrecursive by auto 
        hence "\<exists>p' s'''. validfinpath M s'' p' s''' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> alloccurringstates s'' (fin p') \<subseteq> X \<and> Q a s'''" using alphaffreeandX laststate subsubpath validpath assms(6) assms(7)
          by (subst relentlessly_subpath' [of A Q M _ "recursiveconcpaths succ (laststate s' (succ s'))"]; meson)
      }
      ultimately have "a \<in> alloccurringactions (fin (succ s'))" by blast
      hence "occurs {a} (fin (succ s'))" by auto
      hence "occurs {a} (extendfinpath p (extendfinpath (succ s') (inf (recursiveconcpaths succ (laststate s' (succ s'))))))" by (subst occursright; (subst occursleft)?; simp)
      hence "a \<in> alloccurringactions (inf (conc p (conc (succ s') (recursiveconcpaths succ (laststate s' (succ s'))))))" unfolding extendfinpath.simps occurs_def by blast
      thus "a \<in> alloccurringactions (inf (suffix (Suc n) (recursiveconcpaths succ s)))" using subpath unfoldrecursive by metis
    qed
    hence "validinfpath M s' ?p \<and> \<not>occurs \<alpha>\<^sub>f (inf ?p) \<and> P s' (inf ?p)" using assum2 validpath alphaffreeandX by blast
    moreover have "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)" using assum1 by simp
    moreover have "\<And>p'. validfinpath M s p s' \<and> validinfpath M s' p' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> \<not>occurs \<alpha>\<^sub>f (inf p') \<Longrightarrow> validinfpath M s (conc p p') \<and> \<not>occurs \<alpha>\<^sub>f (inf (conc p p'))" by auto
    moreover have "P s (inf (conc p ?p)) = P (laststate s p) (inf ?p)" by (subst relentlessly_extendpath[of A Q _ B _ p]; simp add: assms(7) assms(8) validfinpathlaststate)
    moreover from this have "validfinpath M s p s'\<Longrightarrow> P s' (inf ?p) = P s (inf (conc p ?p))" by (simp add: validfinpathlaststate)
    ultimately have "\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)" by blast
  }
  moreover {
    assume "s' \<notin> ?S'"
    then obtain p' s'' where "validfinpath M s (p@p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p@p')) \<and> locked M B s''" using assum1 by auto
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'" by blast
  }
  ultimately show "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')
        \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))" by blast
next
  assume "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))"
  moreover {
    assume assum1: "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
    let ?X = "{s. locked M B s}"
    have "\<And>a s. a \<in> -B \<and> locked M B s \<Longrightarrow> \<not>Q a s"
    proof-
      fix a s
      assume "a \<in> -B \<and> locked M B s"
      hence "a \<in> -B \<and> a \<notin> reachableactions M B s" by (simp add: lockednotreachable)
      thus "\<not>Q a s" using assms(5) by auto
    qed
    hence "?X\<subseteq>{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s} \<and> ?X\<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> ?X \<and> alloccurringmap target (fin p) \<subseteq> ?X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> ?X))}" by blast 
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>X\<subseteq>{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s}. X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> X \<and> alloccurringmap target (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X)" using assum1 by blast
  }
  moreover {
    assume "\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)" 
    then obtain p where assum1: "validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)" by auto
    have "\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" by (subst somesuffix_onlyrelentlessly[where ?M="M" and ?s=s]; simp add: assms assum1)
    then obtain n where assum2: "allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" by blast
    let ?X="{s. \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p) \<and> allsuffixes s (inf p) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)}"
    have "?X\<subseteq>{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s}"
      apply (rule subsetI CollectI)+
    proof
      fix s a
      assume "s \<in> ?X"
      then obtain p where inX: "validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p) \<and> allsuffixes s (inf p) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" by auto
      assume inalphaf: "a \<in> \<alpha>\<^sub>f \<inter> - B"
      show "\<not>Q a s"
      proof
        assume "Q a s"
        hence "a \<in> -B \<and> a \<in> A s (inf p)" using inX inalphaf unfolding allsuffixes_def by auto
        hence "a \<in> alloccurringactions (inf p)" using inX unfolding assms(8) allsuffixes_def by auto
        moreover have "a \<notin> alloccurringactions (inf p)" using inX inalphaf by auto
        ultimately show False by simp
      qed
    qed
    moreover have "?X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> ?X \<and> alloccurringmap target (fin p) \<subseteq> ?X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> ?X))}"
      apply (rule subsetI CollectI ballI)+
    proof
      fix s a
      assume "s \<in> ?X"
      then obtain p where inX: "validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p) \<and> allsuffixes s (inf p) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" by auto
      have allstatesinX: "alloccurringstates s (inf p) \<subseteq> ?X"
        unfolding alloccurringstatesalternative
      proof
        fix s'
        assume "s' \<in> insert s {target (ind i (inf p)) | i. i \<in> indicespath (inf p)}"
        hence "s' = s \<or> (\<exists>i. s' = target (p i))" by auto
        moreover have "s' = s \<Longrightarrow> s' \<in> ?X" using inX by auto
        moreover {
          assume "\<exists>i. s' = target (p i)"
          then obtain i where s'eqtarget: "s' = target (p i)" by auto
          have "P s (inf p) = P (source (p (Suc i))) (inf (suffix (Suc i) p))" using inX by (subst relentlessly_infpathsuffix[OF assms(7) assms(8)]; blast)
          hence "P (source (p (Suc i))) (inf (suffix (Suc i) p))" using inX by simp
          moreover have "validinfpath M (source (p (Suc i))) (suffix (Suc i) p) \<and> \<not>occurs \<alpha>\<^sub>f (inf (suffix (Suc i) p)) \<and> allsuffixes (source (p (Suc i))) (inf (suffix (Suc i) p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" apply (subst suffixallsuffixesinf) using inX by auto
          ultimately have "validinfpath M (target (p i)) (suffix (Suc i) p) \<and> \<not>occurs \<alpha>\<^sub>f (inf (suffix (Suc i) p)) \<and> P (target (p i)) (inf (suffix (Suc i) p)) \<and> allsuffixes (target (p i)) (inf (suffix (Suc i) p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" using inX by (simp add: validinfpath_def)
          hence "s' \<in> ?X" using s'eqtarget by blast
        }
        ultimately show "s' \<in> ?X" by auto
      qed  
      assume inBcomp: "a \<in> - B"
      assume "Q a s"
      hence "a \<in> alloccurringactions (inf p)" using inBcomp inX unfolding assms(8) allsuffixes_def by auto
      then obtain i where actionieqa: "action (p i) = a" by auto
      have "alloccurringstates s (fin (prefix i p)) \<subseteq> alloccurringstates s (inf p)" by auto
      hence "s \<in> ?X \<and> alloccurringmap target (fin (prefix i p)) \<subseteq> ?X" using allstatesinX by blast
      moreover have "validfinpath M s (prefix i p) (source (p i))" using inX validinfsubpath by metis
      moreover have "\<not>occurs \<alpha>\<^sub>f (fin (prefix i p))" using inX by auto
      moreover have "p i \<in> transition M" using inX by (simp add: validinfpath_def)
      moreover from this have "(source (p i), a, target (p i)) \<in> transition M \<and> target (p i) \<in> ?X" using allstatesinX actionieqa unfolding alloccurringstatesalternative by auto
      ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s \<in> ?X \<and> alloccurringmap target (fin p) \<subseteq> ?X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> ?X)" by blast
    qed
    moreover have "validfinpath M s (prefix n p) (source (p n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (prefix n p))" using assum1 by auto
    moreover have "source (p n) \<in> ?X"
    proof
      have "P s (inf p) = P (source (p n)) (inf (suffix n p))" using assum1 by (subst relentlessly_infpathsuffix[OF assms(7) assms(8)]; blast)
      hence "P (source (p n)) (inf (suffix n p))" using assum1 by simp
      moreover have "validinfpath M (source (p n)) (suffix n p) \<and> \<not>occurs \<alpha>\<^sub>f (inf (suffix n p)) \<and> allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" using assum1 assum2 by auto
      ultimately show "\<exists>p'. validinfpath M (source (p n)) p' \<and> \<not>occurs \<alpha>\<^sub>f (inf p') \<and> P (source (p n)) (inf p') \<and> allsuffixes (source (p n)) (inf p') (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p)" by blast
    qed
    ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>X\<subseteq>{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s}. X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> X \<and> alloccurringmap target (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X)" by blast
  }
  ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>X\<subseteq>{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s}. X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> X \<and> alloccurringmap target (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X)" by blast
  moreover have "{s. \<forall>a\<in>\<alpha>\<^sub>f \<inter> - B. \<not>Q a s} = \<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e" using assms(9) assms(10) by auto 
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>X\<subseteq>\<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e. X \<subseteq> {s. \<forall>a\<in>- B. Q a s \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s \<in> X \<and> alloccurringmap target (fin p) \<subseteq> X \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s''. (s', a, s'') \<in> transition M \<and> s'' \<in> X))} \<and> s' \<in> X)" by auto
qed

lemma Pformula_withsubformula: 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  and "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s" 
  and "\<And>s. (\<forall>a \<in> -B. \<not>Q a s) \<Longrightarrow> locked M B s"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  and feasible : "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> P s (inf p))"
  and subformula: "\<And>s. s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) f\<rbrakk> M e =
        ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')
        \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))" 
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho> \<cdot> (Acts (-\<alpha>\<^sub>f)\<^sup>\<star>)\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> f)\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p)"
  apply (subst negformula)
  unfolding Diamond.simps(5) apply (subst Diamondmatch)
  apply (subst splitviolating_predicate)
  apply (rule relentlessly_extendpath_valid[OF assms(4) assms(5)])
  unfolding validpath.simps apply blast
  apply (subst freeenabledpath)
  apply (simp add: assms)
  apply (subst subformula)
proof-
  have "\<And>s. (\<exists>p'. validpath M s p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p') =
    ((\<exists>p s''. validfinpath M s p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e))
    \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
    apply (rule freeuntiloccurrenceprogressing_lockedenabled_pred) 
    apply (rule feasible)
    apply (subst relentlessly_extendpath_valid[OF assms(4) assms(5)], blast, simp)
    apply (subst relentlesslyinvarfin[OF assms(2) assms(3) assms(4) assms(5)]; simp)
    done
  hence "(\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> ((\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s' (inf p)))) = 
    (\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> (\<exists>p'. validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' p'))" by blast
  thus "(\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> (((\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'') \<or> (\<exists>p. validinfpath M s' p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s' (inf p))) \<or> (\<exists>p s''. validfinpath M s' p s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s'' \<alpha>\<^sub>e))) = 
    (\<nexists>p p' s'. validfinpath M s p s' \<and> match \<rho> p \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' p')" by blast
qed

lemma Pformula : 
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "\<And>a. \<not>dependvar (\<phi>_on a) M 0"
  and "\<not>dependvar \<phi>_off M 0"
  and "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s" 
  and "\<And>s. (\<forall>a \<in> -B. \<not> Q a s) \<Longrightarrow> locked M B s"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  and "\<And>s a. a \<in> -B \<Longrightarrow> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e = Q a s"
  and "\<And>s. s \<in> \<lbrakk>shiftdown \<phi>_off 0\<rbrakk> M e = (\<forall>a \<in> \<alpha>\<^sub>f -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e)"
  and "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho> \<cdot> (Acts (-\<alpha>\<^sub>f)\<^sup>\<star>)\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<nu> \<phi>_off \<and>\<^sub>\<mu> (\<And>\<^sub>\<mu>a\<in>-B. \<phi>_on a \<Longrightarrow>\<^sub>R (\<mu> var 1 \<and>\<^sub>\<mu> (\<langle>a\<rangle>\<^sub>\<mu>var 1 \<or>\<^sub>\<mu> \<langle>Acts (-\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)))))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and>  P s p)"
  apply (subst Pformula_withsubformula [OF _ assms(4, 5, 6, 7)]; (rule Psubformula [OF assms(1) _ assms(2, 3, 4, 5, 6, 7, 8, 9)])?; (simp add: assms(10))?)
  apply (rule P_feasible[OF _ assms(4, 5, 6, 7)]; simp add: assms)
  done 

lemma finiteBcomp [simp]: "finite A \<or> finite (-B) \<Longrightarrow> finite (A - B)"
proof-
  assume "finite A \<or> finite (-B)"
  hence "finite (A \<inter> -B)" by simp
  moreover have "A \<inter> -B = A - B" by auto
  ultimately show ?thesis by simp
qed

lemma SFAformula : 
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho> \<cdot> (Acts (-\<alpha>\<^sub>f)\<^sup>\<star>)\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<nu> [Acts (\<alpha>\<^sub>f -B)]\<^sub>R ff \<and>\<^sub>\<mu> (\<And>\<^sub>\<mu>a \<in> -B. \<langle>a\<rangle>\<^sub>\<mu>tt \<Longrightarrow>\<^sub>R (\<mu> var 1 \<and>\<^sub>\<mu> (\<langle>a\<rangle>\<^sub>\<mu> var 1 \<or>\<^sub>\<mu> \<langle>Acts (-\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)))))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> SFA M B s p)"
  apply (rule Pformula[where ?Q="\<lambda>a s. a \<in> enabledactions M s" and ?A="\<lambda>s p. relentlesslyenabled M s p"]; (rule notoccursnotdepends)?; (simp only: assms(2))?)
  unfolding SFA_def
  using assms(1) apply simp
  apply simp
  apply simp
  using enabled_reachable subset_iff apply metis
  unfolding locked_def apply blast
  apply (simp add: relentlesslyenabled_def)+
  unfolding Boxmatch apply (subst matchunfoldActs, simp add: assms)
proof-
  fix s
  have "(\<forall>p s'. validfinpath M s p s' \<and> (\<exists>t. p = [t] \<and> action t \<in> \<alpha>\<^sub>f -B) \<longrightarrow> s' \<in> \<lbrakk>ff\<rbrakk> M e) = (\<forall>p s'. validfinpath M s p s' \<and> (\<exists>t. p = [t] \<and> action t \<in> \<alpha>\<^sub>f -B) \<longrightarrow> False)" by simp
  moreover have "... = (\<forall>p s' t. validfinpath M s p s' \<and> p = [t] \<and> action t \<in> \<alpha>\<^sub>f -B \<longrightarrow> False)" by blast
  ultimately show "(\<forall>p s'. validfinpath M s p s' \<and> (\<exists>t. p = [t] \<and> action t \<in> \<alpha>\<^sub>f -B) \<longrightarrow> s' \<in> \<lbrakk>ff\<rbrakk> M e) = (\<forall>a\<in>\<alpha>\<^sub>f -B. \<forall>s'. (s, a, s') \<notin> transition M)" by auto
qed

lemma SHFAformula : 
  fixes M :: "('a, 's) lts"
  assumes "finite (UNIV :: 's set)"
  and "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>\<not>\<^sub>\<mu>\<langle>\<rho> \<cdot> (Acts (-\<alpha>\<^sub>f)\<^sup>\<star>)\<rangle>\<^sub>R (\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt \<or>\<^sub>\<mu> (\<nu> [Acts (-B)\<^sup>\<star> \<cdot> Acts (\<alpha>\<^sub>f -B)]\<^sub>R ff \<and>\<^sub>\<mu> (\<And>\<^sub>\<mu>a \<in> -B. \<langle>Acts (-B)\<^sup>\<star> \<cdot> {a}\<^sub>R\<rangle>\<^sub>R tt \<Longrightarrow>\<^sub>R (\<mu> var 1 \<and>\<^sub>\<mu> (\<langle>a\<rangle>\<^sub>\<mu> var 1 \<or>\<^sub>\<mu> \<langle>Acts (-\<alpha>\<^sub>f)\<rangle>\<^sub>R var 0)))))\<rbrakk> M e =
  (\<nexists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> SHFA M B s p)"
  apply (rule Pformula[where ?Q="\<lambda>a s. a \<in> reachableactions M B s" and ?A="\<lambda>s p. relentlesslyreachable M B s p"]; (rule notoccursnotdepends)?; (simp only: assms(2) shiftdownDiamond shiftdownBox shiftdown.simps)?)
  unfolding SHFA_def
  using assms(1) apply simp+
  using notreachable_locked apply metis
  apply (simp add: relentlesslyreachable_def)
  apply simp
proof-
  have res1: "\<And>a. \<lbrakk>Diamond (Times (Star (Acts (-B))) (Atom a)) tt\<rbrakk> M e = \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e" by simp
  moreover have res2: "\<And>s a. s \<in> \<lbrakk>Diamond (Star (Acts (-B))) (diamond a tt)\<rbrakk> M e = (a \<in> reachableactions M B s)" using assms(2) Diamondreachable by metis
  ultimately show "\<And>s a. a \<in> - B \<Longrightarrow> (s \<in> \<lbrakk>Diamond (Times (Star (Acts (-B))) (Atom a)) tt\<rbrakk> M e) = (a \<in> reachableactions M B s)" by blast
  have "\<And>s. s \<in> \<lbrakk>Box (Acts (\<alpha>\<^sub>f -B)) ff\<rbrakk> M e = (\<forall>a\<in>\<alpha>\<^sub>f -B. s \<in> \<lbrakk>Box (Atom a) ff\<rbrakk> M e)" by (auto simp: assms(2))
  hence "\<And>s. s \<in> \<lbrakk>Box (Times (Star (Acts (-B))) (Acts (\<alpha>\<^sub>f -B))) ff\<rbrakk> M e = (\<forall>a\<in>\<alpha>\<^sub>f -B. s \<in> \<lbrakk>Box (Star (Acts (-B))) (Box (Atom a) ff)\<rbrakk> M e)"
    apply (simp only: Box.simps(5))
    apply (simp only: Boxmatch matchstaract reachableactionsdef)
    using Boxmatch apply blast
    done
  hence "\<And>s. (s \<in> \<lbrakk>Box (Times (Star (Acts (-B))) (Acts (\<alpha>\<^sub>f -B))) ff\<rbrakk> M e) = (\<forall>a\<in>\<alpha>\<^sub>f -B. s \<in> \<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e)" by (simp only: Box.simps)
  moreover have "\<And>s a. s \<in> \<lbrakk>Box (Star (Acts (-B))) (box a ff)\<rbrakk> M e = (a \<notin> reachableactions M B s)" using Boxnotreachable assms(2) by metis
  ultimately show "\<And>s. (s \<in> \<lbrakk>Box (Times (Star (Acts (-B))) (Acts (\<alpha>\<^sub>f -B))) ff\<rbrakk> M e) = (\<forall>a\<in>\<alpha>\<^sub>f -B. s \<notin> \<lbrakk>Diamond (Times (Star (Acts (-B))) (Atom a)) tt\<rbrakk> M e)" using res1 res2 by blast
qed

end