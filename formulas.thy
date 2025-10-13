theory formulas
imports paths Main
begin

lemma prop40rtl :
  assumes "\<not> dependvar f M 0"
  and "\<not> dependvar g M 0"
  and "finite A"
  and "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A
     \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e"
  shows "s \<in> \<lbrakk>mu (and' g (or f (Diamond (Acts A) (var 0))))\<rbrakk> M e"
  apply (simp add: assms(3))
  apply (rule allI)
proof
  fix S'
  from assms(4) obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A
     \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by auto
  assume assum2: "\<lbrakk>g\<rbrakk> M (newenvironment e S') \<inter> 
    (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S' "
  have inS' : "validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A
     \<and> insert s (set (map target p)) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S'"
    apply (induct p arbitrary : s; simp)
  proof
    fix t p s
    assume assum3 : "(\<And>s. validfinpath M s p s' \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S')"
    assume assum4 : "s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S'"
    hence "target t \<in> S'" using assum3 by auto
    hence "(source t, action t, target t) \<in> transition M \<and> target t \<in> S'" using assum4 splittransition by metis
    hence "source t \<in> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assum4 by blast
    moreover have "source t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e" using assum4 by auto
    moreover from this have "source t \<in> \<lbrakk>g\<rbrakk> M (newenvironment e S')" using notdependshiftdown assms(2) by metis
    ultimately show "source t \<in> S'" using assum2 by auto
  qed
  have "validfinpath M s p s' \<longrightarrow> s' \<in> insert s (set (map target p))" by (induct p arbitrary: s; simp)
  hence "s' \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" using assum1 by auto
  hence "s' \<in> \<lbrakk>g\<rbrakk> M (newenvironment e S') \<and> s' \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S')" by (simp add: assms(1) assms(2) notdependshiftdown)
  thus "s \<in> S'" using assum1 assum2 inS' by auto
qed

lemma prop40ltrinbetween :
  assumes "\<not>dependvar f M 0"
  and "\<not>dependvar g M 0"
  and "finite A"
  shows "s \<in> ((transformer (and' g (or f (Diamond (Acts A) (var 0)))) M e)^^n){} \<longrightarrow>
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A
     \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e)"
  apply (induct n arbitrary : s)
  apply (simp)
proof
  fix n s
  let ?f = "and' g (or f (Diamond (Acts A) (var 0)))"
  let ?S' = "(transformer ?f M e ^^ n) {}"
  assume assum1 : "\<And>s. s \<in> ?S'
    \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e)"
  let ?S'' = "(transformer ?f M e ^^ Suc n) {}"
  assume assum2 : "s \<in> ?S''"
  hence splitand : "s \<in> \<lbrakk>g\<rbrakk> M (newenvironment e ?S') 
    \<and> (s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'))" by (simp add: transformer_def assms(3) del: Diamond.simps)
  hence ing : "s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e" using notdependshiftdown assms by metis
  from splitand have "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S')" by auto
  moreover {
    assume assum3 : "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e ?S')"
    from assum3 have "s \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e)" by (metis assms(1) notdependshiftdown)
    hence "validfinpath M s [] s \<and> s \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> (action ` set [] \<subseteq> A) \<and> s \<in> (\<lbrakk>shiftdown g 0\<rbrakk> M e) \<and> (target ` set []) \<subseteq> (\<lbrakk>shiftdown g 0\<rbrakk> M e)" using ing by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A \<and> s \<in> (\<lbrakk>shiftdown g 0\<rbrakk> M e) \<and> (target ` set p) \<subseteq> (\<lbrakk>shiftdown g 0\<rbrakk> M e)" by blast
  }
  moreover {
    assume "\<exists>s' a. a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> ?S'"
    then obtain s' a where assum3 : "a \<in> A \<and> (s, a, s') \<in> transition M \<and> s' \<in> ?S'" by auto
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e)" using assum1 by auto
    then obtain p s'' where tail : "validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (\<lbrakk>shiftdown g 0\<rbrakk> M e) \<and> target ` set p \<subseteq> (\<lbrakk>shiftdown g 0\<rbrakk> M e))" by auto
    let ?p = "(s, a, s') # p"
    have "source (s, a, s') = s \<and> (s, a, s') \<in> transition M \<and> validfinpath M (target (s, a, s')) p s''" using assum3 tail by simp
    hence "validfinpath M s ?p s''" by auto
    hence "validfinpath M s ?p s'' \<and> s'' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> (action ` set ?p \<subseteq> A) \<and> 
      s \<in> (\<lbrakk>shiftdown g 0\<rbrakk> M e) \<and> target ` set ?p \<subseteq> (\<lbrakk>shiftdown g 0\<rbrakk> M e)" using assum3 ing tail by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A 
      \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A
      \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e" by (simp; blast)
qed

lemma prop40ltr :
  fixes M :: "('a, 's) lts"
  assumes "s \<in> \<lbrakk>mu (and' g (or (f) (Diamond (Acts A) (var 0))))\<rbrakk> M e"
  and "\<not>dependvar f M 0"
  and "\<not>dependvar g M 0"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) 
        \<and> alloccurringactions (fin p) \<subseteq> A 
        \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e"
proof-
  have "mono (transformer (and' g (or f (Diamond (Acts A) (var 0)))) M e)" by (rule monotonicitynotdependcoro(1); simp add: assms notdepends)
  hence "s \<in> ((transformer (and' g (or f (Diamond (Acts A) (var 0)))) M e)^^(card (UNIV :: 's set))){}" using assms(1) assms(4) transformer_eq_mu by auto 
  thus ?thesis using prop40ltrinbetween assms(2) assms(3) assms(5) by metis
qed

proposition proposition40 :
  fixes M :: "('a, 's) lts"
  assumes "\<not> dependvar f M 0"
  and "\<not> dependvar g M 0"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "s \<in> \<lbrakk>mu (and' g (or f (Diamond (Acts A) (var 0))))\<rbrakk> M e = 
    (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A  
      \<and> alloccurringstates s (fin p) \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e)"
  apply (rule iffI)
  apply (rule prop40ltr; simp add: assms)
  apply (rule prop40rtl; simp add: assms)
  done

lemma invariantApath : 
  assumes "\<not> dependvar f M 0"
  and "S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}"
  and "s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and>  alloccurringactions (fin p) \<subseteq> A}"
  shows "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A}"
proof-
  have "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assms(2) assms(3) by auto
  hence "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<or>  (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S')" using assms(2) by auto
  moreover have "s \<notin> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" using assms(1) notdependshiftdown by metis
    hence "validfinpath M s [] s \<and> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and>  alloccurringactions (fin []) \<subseteq> A" by auto
    thus False using assms(3) by blast
  qed
  ultimately have "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  then obtain act s' where assum1 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> (set (map action p) \<subseteq> A)"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "\<exists>p s''. s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A"
    then obtain p s'' where "s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A" by auto
    hence "validfinpath M s ((s, act, s')#p) s'' \<and> s'' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> alloccurringactions (fin ((s, act, s')#p)) \<subseteq> A" using assum1 by simp
    thus False using assms(3) by blast
  qed
  thus ?thesis using assum1 by auto
qed

lemma theorem21generalizedltr : 
  assumes "\<not> dependvar f M 0"
  and "finite A"
  and "s \<in> \<lbrakk>nu (or f (Diamond (Acts A) (var 0)))\<rbrakk> M e"
  shows "((\<exists>p s'. validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e)) \<or>
    (\<exists>p. validinfpath M s p \<and>  alloccurringactions (inf p) \<subseteq> A))"
proof-
  have "\<exists>S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(2) assms(3) by (simp del: Diamond.simps)
  then obtain S' where assum1 : "S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" by auto
  have "(\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> alloccurringactions (fin p) \<subseteq> A) \<Longrightarrow>  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))"
    apply (rule successorlemma)
  proof-
    assume assum2 : "\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A"
    let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e) \<and> alloccurringactions (fin p) \<subseteq> A}" 
    have "(\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))"
      apply (rule allI)
    proof
      fix s
      assume assum3 : "s \<in> ?S'"
      have "\<not> dependvar f M 0 \<Longrightarrow> S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<Longrightarrow> s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A} \<Longrightarrow> \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> alloccurringactions (fin p) \<subseteq> A}" using invariantApath by simp
      hence "\<exists>s'' act. act \<in> A \<and> (s, act, s'') \<in> (transition M) \<and> s'' \<in> ?S'" using assum1 assum3 assms(1) by simp
      thus "\<exists>t. source t = s \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S'" by auto
    qed
    moreover have "s \<in> ?S'" using assum1 assum2 by auto
    ultimately show "s \<in> ?S' \<and> (\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))" by simp
  qed
  thus ?thesis by (simp only: image_subset_iff alloccurringmap.simps; auto)
qed

lemma theorem21generalizedrtl : 
  assumes "\<not> dependvar f M 0"
  and "finite A"
  and "(\<exists>p s'. validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e)) \<or>
     (\<exists>p. validinfpath M s p \<and>  alloccurringactions (inf p) \<subseteq> A)" 
  shows "s \<in> \<lbrakk>nu (or f (Diamond (Acts A) (var 0)))\<rbrakk> M e"
  apply (simp add: assms(2) del: Diamond.simps)
  apply (subst notdependshiftdown)
  apply (simp add: assms(1))
  apply (rule exI)
proof
  let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> (set (map action p) \<subseteq> A) \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e)) \<or>
              (\<exists>p. validinfpath M s p \<and> image action (range p) \<subseteq> A)}"
  show "s \<in> ?S'" using assms(3) by simp
  show "?S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}"
  proof
    fix s
    assume "s \<in> ?S'"
    moreover {  
      assume "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A"
      then obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A" by auto
      have "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A \<Longrightarrow> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A))"
        apply (induct p arbitrary : s)
        apply (simp_all add: validfinpath.cases)
      proof-
        fix t p
        (*assum2 only needed for base case?*)
        assume assum3 : "t \<in> transition M \<and> validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A"
        hence "(source t, action t, target t) \<in> transition M \<and> (validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A)" using splittransition by metis
        thus "source t \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (source t, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A))" by blast
      qed
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by auto
    }
    moreover {
      assume "\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)"
      then obtain p where assum1 : "validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)" by auto
      hence "s = source (p 0) \<and> (p 0) \<in> transition M \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by (simp add: validinfpath_def)
      hence "(s, action (p 0), target (p 0)) \<in> transition M  \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by simp
      hence "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and>  (\<exists>p. validinfpath M s' p \<and> (\<forall>n. action (p n) \<in> A))" by blast
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by blast
   }
   ultimately show "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" by blast
 qed
qed

lemma theorem21generalized :  
  assumes "\<not> dependvar f M 0"
  and "finite A"
  shows "(s \<in> \<lbrakk>nu (or f (Diamond (Acts A) (var 0)))\<rbrakk> M e) =
  ((\<exists>p s'. validfinpath M s p s' \<and> alloccurringactions (fin p) \<subseteq> A \<and> s' \<in> (\<lbrakk>shiftdown f 0\<rbrakk> M e)) \<or> 
  (\<exists>p. validinfpath M s p \<and> alloccurringactions (inf p) \<subseteq> A))"
  apply (rule iffI)
  apply (rule theorem21generalizedltr; simp add: assms)
  apply (rule theorem21generalizedrtl; simp add: assms)
  done

lemma negformula [simp] : "(s \<in> \<lbrakk>neg f\<rbrakk> M e) = (s \<notin> \<lbrakk>f\<rbrakk> M e)" by simp

lemma notoccursfin [simp] : "action ` set p \<subseteq> -\<alpha>\<^sub>f = (\<not> occurs \<alpha>\<^sub>f (fin p))" by auto

lemma notoccursinf [simp] : "action ` range p \<subseteq> -\<alpha>\<^sub>f = (\<not> occurs \<alpha>\<^sub>f (inf p))" by auto

theorem theorem21 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (-B)) ff)) (Diamond (Acts (-\<alpha>\<^sub>f)) (var 0)))))\<rbrakk> M e 
    = (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p)"
  apply (subst negformula)
proof-
  have "\<forall>s. s \<in> \<lbrakk>Diamond \<rho> (nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (-B)) ff)) (Diamond (Acts (-\<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e 
    = (\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p )"
    apply (subst Diamondmatch)
    apply (simp add: assms del: formulasemantics.simps)
  proof
    let ?A = "\<lambda>s'. s' \<in> \<lbrakk>nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (- B)) ff)) (Diamond (Acts (- \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M e"
    let ?B = "\<lambda>s'.  (\<exists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not> occurs \<alpha>\<^sub>f (inf p))"
    let ?C = "\<lambda>s'. (\<exists> p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p)"
    have res1 : "\<forall>s'. ?A s' = ?B s'"
      apply (subst theorem21generalized; simp add: assms notoccursnotdepends Boxcomplement_locked Diamond_enabled del: Diamond.simps Box.simps Diamond_eq_exist Box_eq_forall occurssimps)
      apply auto
      done
    have res2: "\<forall>s'. ?C s' = ?B s'" by (subst freeuntiloccurrenceprogressing_lockedenabled; simp)
    have "\<forall>s'. ?A s' = ?C s'" by (subst res2; subst res1; auto)
    thus "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> s' \<in> \<lbrakk>nu (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (-B)) ff)) (Diamond (Acts (-\<alpha>\<^sub>f)) (var 0)))\<rbrakk> M e) = (\<exists>p. match \<rho> p \<and> (\<exists>p' s'. validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'))" by blast    
  qed
  thus "(s \<notin> \<lbrakk>Diamond \<rho> (nu (formula.or (formula.or (Diamond (Acts \<alpha>\<^sub>e) tt) (Box (Acts (- B)) ff)) (Diamond (Acts (- \<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e) = (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p)" by blast
qed

lemma lemma50 : 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (\<alpha>\<^sub>_el a)"
  and "\<not>dependvar (\<phi>_off a) M 0"
  shows "s \<in> \<lbrakk>Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (Acts ((\<alpha>\<^sub>_el a) -\<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S') 
    = (\<exists>p s'. validfinpath M s p s' \<and> (\<not> occurs \<alpha>\<^sub>f (fin p) \<and> 
        ((enabled M s' \<alpha>\<^sub>e) \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> ((\<alpha>\<^sub>_el a) - \<alpha>\<^sub>f) \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')) ))"
  apply (subst Diamondmatch)
  apply (simp add: assms enabled_def)
  apply (subst matchstaract)
  apply (simp del: Diamond.simps add: assms)
  apply (subst notdependshiftdown; simp add: assms)
  apply meson
  done 
                                 
lemma occursactionorstate : 
  assumes "\<forall>s'. ((\<exists>p' s''. validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'') \<longrightarrow> s' \<in> S')"
  and "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<and> (occurs A (fin p) \<or> occursstate S'' s (fin p))"
  shows "\<exists>p' s'. validfinpath M s p' s' \<and> ((s' \<in> S' \<inter> S'') \<or> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> A \<and> s'' \<in> S'))"
proof-
  have "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<Longrightarrow> (\<forall>i < length p. source (p!i) \<in> S')"
    apply rule
  proof
    fix i
    assume assum1 : "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
    assume "i < length p"
    hence "validfinpath M (source (p!i)) (drop i p) s' \<and> locked M B s'" using assum1 by auto
    moreover have "\<not> occurs \<alpha>\<^sub>f (fin (drop i p))" unfolding notoccursfin using assum1 set_drop_subset by fastforce
    ultimately show "source (p!i) \<in> S'" using assms by blast
  qed
  hence "\<forall>i < length p. source (p!i) \<in> S'" using assms by auto
  hence "source ` set p \<subseteq> S'" by (metis image_subsetI in_set_conv_nth)
  moreover have "s' \<in> S'"
  proof-
    have "validfinpath M s' [] s' \<and> \<not>occurs \<alpha>\<^sub>f (fin []) \<and> locked M B s'" using assms by auto
    thus "s' \<in> S'" using assms by metis
  qed
  ultimately have "insert s' (set (map source p)) \<subseteq> S'" by simp
  moreover have "validfinpath M s p s' \<longrightarrow> (insert s' (set (map source p)) \<subseteq> S') = (insert s (set (map target p)) \<subseteq> S')" by (induct p arbitrary: s; simp; blast)
  ultimately have allstatesinS' : "s \<in> S' \<and> (\<forall>i< length p. target (p!i) \<in> S')" by (simp add: subset_iff assms)
  {
    assume assum1: "validfinpath M s p s' \<and> occurs A (fin p)"
    hence "\<exists> a \<in> A. a \<in> (set (map action p))" by simp
    then obtain a where assum2: "a \<in> A \<and> a \<in> (set (map action p))" by auto
    have "a \<in> (set (map action p)) \<longrightarrow> (\<exists>i < length p. a = action (p!i))" by (induction p; auto)
    then obtain i where "i < length p \<and> a = action (p!i)" using assum2 by auto
    hence "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M \<and> action (p!i) \<in> A \<and> target (p!i) \<in> S'" using assum1 assum2 allstatesinS' by auto
    hence "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> A \<and> s'' \<in> S')" by blast
  }
  moreover {
    assume assum1: "validfinpath M s p s' \<and> occursstate S'' s (fin p)"
    hence "\<exists>s' \<in> S''. s' \<in> insert s (set (map target p))" by simp
    then obtain s' where assum2: "s' \<in> S'' \<and> s' \<in> insert s (set (map target p))" by auto
    have "s' \<in> insert s (set (map target p)) \<longrightarrow> s' = s \<or> (\<exists>i < length p. s' = target (p!i))" by (induction p; auto)
    hence "s' = s \<or> (\<exists>i < length p. s' = target (p!i))" using assum2 by auto
    moreover have "s' = s \<Longrightarrow> validfinpath M s [] s \<and> s \<in> S' \<inter> S''"using assum2 assum1 allstatesinS' by auto
    moreover {
      assume "\<exists>i < length p. s' = target (p!i)" 
      then obtain i where assum3 : "i < length p \<and> s'= target (p!i)" by auto
      hence "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M" using assum1 by auto
      hence "validfinpath M s ((take i p) @ [(source (p!i), action (p!i), target (p!i))]) (target (p!i)) \<and> (target (p!i)) \<in> S''" using assum2 assum3 by simp
      moreover have "(target (p!i)) \<in> S'" using assum1 assum3 allstatesinS' by auto
      ultimately have "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" by blast
    }
    ultimately have "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" by blast
  }
  ultimately show ?thesis using assms by blast
qed

lemma addpathsnotoccurs: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<Longrightarrow> validfinpath M s (p @ p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p @ p'))"
  by auto       

lemma notemptypath : "s \<notin> S' \<and> (occursstate S' s (fin p) \<or> occurs A (fin p)) \<longrightarrow> p \<noteq> []" 
  by (cases p; simp)

lemma existssplitpath :
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate (succ s) \<in> S')" 
  shows "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))"
  apply (induct i)
proof-
  have "succ s \<noteq> [] \<Longrightarrow> recursiveconcpaths succ s = conc (succ s) (recursiveconcpaths succ (laststate (succ s)))" by (rule; simp)
  hence "0 < length (succ s) \<and> s \<in> S' \<and> suffix 0 (recursiveconcpaths succ s) = conc (drop 0 (succ s)) (recursiveconcpaths succ (laststate (succ s)))" using assms by auto
  thus "\<exists>j s'. j < length (succ s') \<and>  s' \<in> S' \<and> suffix 0 (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" by blast
next
  fix i
  assume "\<exists>j s'. j < length (succ s') \<and>  s' \<in> S' \<and> suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))"
  then obtain j s' where IH: "j < length (succ s') \<and>  s' \<in> S' \<and> suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" by auto
  have "suffix (Suc i) (recursiveconcpaths succ s) = suffix (Suc 0) (suffix i (recursiveconcpaths succ s))" by auto
  moreover have "... = (conc (drop (Suc j) (succ s')) (recursiveconcpaths succ (laststate (succ s'))))" using IH by auto
  ultimately have IH: "j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) = (conc (drop (Suc j) (succ s')) (recursiveconcpaths succ (laststate (succ s'))))" using IH by simp
  {
    assume assum2: "Suc j < length (succ s')"
    hence "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" using IH by auto
  }
  moreover {
    assume assum2: "Suc j \<ge> length (succ s')"
    let ?s = "laststate (succ s')"
    have "suffix (Suc i) (recursiveconcpaths succ s) = recursiveconcpaths succ ?s" using assum2 IH by auto
    moreover have "succ ?s \<noteq> [] \<Longrightarrow> recursiveconcpaths succ ?s= conc (succ ?s) (recursiveconcpaths succ (laststate (succ ?s)))" by (rule; simp)
    moreover have "succ ?s \<noteq> []" using assms IH by auto
    ultimately have "0 < length (succ ?s) \<and> suffix (Suc i) (recursiveconcpaths succ s) = conc (succ ?s) (recursiveconcpaths succ (laststate (succ ?s)))" by simp
    moreover have "drop 0 (succ ?s) = succ ?s" by auto
    ultimately have "0 < length (succ ?s) \<and> ?s \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) = conc (drop 0 (succ ?s)) (recursiveconcpaths succ (laststate (succ ?s)))" using assms IH by metis
    hence "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" by blast
  }
  ultimately show "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" using not_le_imp_less by auto
qed

lemma feasiblesublemma :
  assumes exclusive: "\<And>s a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e "
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and feasible: "\<And>s a. s \<in> S' \<and> a \<in> -B \<Longrightarrow> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)))"
  and "finite (-B)"
  and "\<exists>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "s \<in> S' \<Longrightarrow> \<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))"
proof-
  assume assum1 : "s \<in> S'"
  let ?L = "{a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e}"
  have "\<forall>n. \<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow> (\<exists>p s'. (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
  proof
    fix n
    show "\<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow> (\<exists>p s'. (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
      apply (induct n; rule allI; rule impI)
    proof-
      let ?p = "[]"
      fix L 
      assume assum2 : "card L = 0 \<and> L \<subseteq> ?L"
      hence "L \<subseteq> (-B) \<and> finite (-B)" using assms(4) by auto
      hence "finite L" using finite_subset by auto
      hence "L = {}" using assum2 by auto
      hence "(L \<noteq> {} \<longrightarrow> ?p \<noteq> []) \<and> validfinpath M s ?p s \<and> s \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin []) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin ?p ) \<or> occurs (\<alpha>_el a) (fin ?p))" using assum1 by auto
      thus "\<exists>p s'. (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
    next
      fix n 
      fix L
      assume IH : "\<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow> (\<exists>p s'. (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
      assume "card L = Suc n \<and> L \<subseteq> ?L"
      then obtain a L' where assum2: "L = insert a L' \<and> a \<notin> L' \<and> card L' = n \<and> L \<subseteq> ?L" using card_eq_SucD by metis
      then obtain p s' where assum3: "(L' \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L' \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using IH by blast
      have "(occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p)) \<or> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el a) (fin p))" by auto
      moreover {
        assume "occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p)"
        (*if we have that B is not the entire set, do we need exclusive?*)
        hence "p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using exclusive notemptypath assum2 assum3 by auto
        hence "\<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto
      }
      moreover {
        have sinpihon: "s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e" using assum2 by blast
        assume assum4 : "\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<and> \<not>occurs (\<alpha>_el a) (fin p)"
        moreover have ainBcomp : "a \<in> -B" using assum2 by auto
        ultimately obtain p' s'' where "validfinpath M s' p' s'' \<and> s'' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> ((occurs (\<alpha>_el a) (fin p') \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p')))" using persistent assum3 feasible sinpihon by metis
        moreover then have "p' \<noteq> []" using ainBcomp assum3 assum4 exclusive notemptypath persistent sinpihon by metis
        moreover have "validfinpath M s p s' \<and> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p') \<Longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (extendfinpath p (fin p'))" by (rule occursstaterightvalidpath)
        moreover have "occurs (\<alpha>_el a) (fin p') \<Longrightarrow> occurs (\<alpha>_el a) (fin (p @ p'))" by auto
        ultimately have "p @ p' \<noteq> [] \<and> validfinpath M s (p @ p') s'' \<and> s'' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin (p @ p')) \<and> (occurs (\<alpha>_el a) (fin (p @ p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin (p @ p')))" using assum3 by auto
        moreover have "\<forall>a. a \<in> L' \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (extendfinpath p (fin p')) \<or> occurs (\<alpha>_el a) (fin p)" using assum3 occursstateleft by metis
        moreover then have "\<forall>a. a \<in> L' \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin (p @ p')) \<or> occurs (\<alpha>_el a) (fin (p @ p'))" by auto
        ultimately have "p @ p' \<noteq> [] \<and> validfinpath M s (p @ p') s'' \<and>  s'' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin (p @ p')) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin (p @ p')) \<or> occurs (\<alpha>_el a) (fin (p @ p')))" using assum2 assum3 by auto
        hence "\<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
      }
      ultimately show "\<exists>p s'. (L \<noteq> {} \<longrightarrow> p \<noteq> [])  \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
    qed
  qed
  moreover have "?L \<noteq> {}" using assms(5) by auto
  ultimately have  "\<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> ?L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
  thus ?thesis by auto
qed

lemma constructfairpath :
  assumes exclusive: "\<forall>s. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e "
  and persistent: "\<forall>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and reachable: "\<forall>s \<in> S'. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)))"
  and "finite (-B)"
  and "\<forall>s \<in> S'. \<exists>a\<in>- B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "s \<in> S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
proof-
  assume assum1: "s \<in> S'"
  have "\<forall>s \<in> S'. \<exists>p. p \<noteq> [] \<and> validfinpath M s p (laststate p) \<and> laststate p \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" 
  (is "\<forall>s \<in> S'. ?P s")
  proof
    fix s
    assume "s \<in> S'"
    hence "\<exists>p s'. p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" 
      apply (subst feasiblesublemma)
      using  exclusive persistent reachable assms(4) assms(5) apply blast+
      done
    then obtain p s' where "p \<noteq> [] \<and> validfinpath M s p s' \<and> s' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto
    thus "?P s" using validfinpathlaststate by metis
  qed
  then obtain succ where assum2: "\<forall>s' \<in> S'. succ s' \<noteq> [] \<and> validfinpath M s' (succ s') (laststate (succ s')) \<and> laststate (succ s') \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s')) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin (succ s')) \<or> occurs (\<alpha>_el a) (fin (succ s')))" by metis
  let ?p = "recursiveconcpaths succ s"
  have validinfpath: "validinfpath M s ?p" using validinfpathconc assum1 assum2 by metis
  moreover have "\<not> occurs \<alpha>\<^sub>f (inf ?p)" 
    apply (subst occursinfalternative) 
    apply (subst validpredconc [where ?P="\<lambda>s. \<lambda>t. action (t) \<notin> \<alpha>\<^sub>f" and ?Q="\<lambda>s. \<lambda>p. \<not>occurs \<alpha>\<^sub>f (fin p)"])
    using assum1 assum2 apply auto
    done
  moreover have "\<forall>a \<in> -B. ((\<forall>i. (source (?p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p)))))"
    apply (rule ballI allI)+
  proof
    fix a i
    assume ainBcomp: "a \<in> -B"
    assume phion: "source (?p i) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
   (*opschonen*)
    obtain j s' where assum3: "s' \<in> S' \<and> j < length (succ s') \<and> suffix i ?p = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')))" using suffix_recursiveconcpaths assum1 assum2 by metis
    have "validinfpath M (source (?p i)) (suffix i ?p)" using validinfpath validinfsubpathright by metis
    moreover have "drop j (succ s') \<noteq> [] \<and> laststate (drop j (succ s')) = laststate (succ s')" using assum3 by auto
    ultimately have "validfinpath M (source (?p i)) (drop j (succ s')) (laststate (succ s'))" using validinfpathsplitlaststate assum3 by metis
    { 
      moreover assume "\<not>occurs (\<alpha>_el a) (fin (drop j (succ s'))) \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s')))"
      ultimately have "laststate (succ s') \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e" using persistent ainBcomp phion by metis
      hence "occurs (\<alpha>_el a) (fin (succ (laststate (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s'))))" using ainBcomp assum2 assum3 by blast
    }
    hence "occurs (\<alpha>_el a) (fin (drop j (succ s'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s'))) \<or> occurs (\<alpha>_el a) (fin (succ (laststate (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s'))))" by blast
    hence "occurs (\<alpha>_el a) (fin (drop j (succ s'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s'))) \<or>
       occurs (\<alpha>_el a) (fin (succ (laststate (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s'))))" by blast
    moreover have "drop j (succ s') \<noteq> [] \<and> laststate (succ s') = laststate (drop j (succ s'))" using assum3 by auto
    ultimately have "occurs (\<alpha>_el a) (extendfinpath (drop j (succ s')) (fin (succ (laststate (succ s'))))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (extendfinpath (drop j (succ s')) (fin (succ (laststate (succ s')))))" 
      using occursleft occursstateleft occursright occursstateright by metis
    hence res1: "occurs (\<alpha>_el a) (fin (drop j (succ s') @ (succ (laststate (succ s'))))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s') @ (succ (laststate (succ s')))))" by simp
    have "inf (suffix i ?p) = extendfinpath (drop j (succ s')) (inf (recursiveconcpaths succ (laststate (succ s'))))" using assum3 by auto
    moreover have "succ (laststate (succ s')) \<noteq> []" using assum2 assum3 by auto    
    ultimately have "inf (suffix i ?p) = extendfinpath ((drop j (succ s')) @ (succ (laststate (succ s')))) (inf (recursiveconcpaths succ (laststate (succ (laststate (succ s'))))))" by (simp add: unfoldrecursiveconcpaths extendfinpath_extendfinpath)
    thus "occurs (\<alpha>_el a) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))"  using occursleft occursstateleft res1 by metis
  qed
  ultimately show ?thesis by blast
qed

lemma infpathoccursoroccursstate : 
  assumes "validinfpath M s p \<and> (occurs A (inf p) \<or> occursstate S' s (inf p))"
  shows "\<exists>i. source (p i) \<in> S' \<or> action (p i) \<in> A" 
  using assms ind.simps(2) occursinfalternative occursstatealternative validinfpath_def by metis

lemma theorem24_subformula :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>a. finite (\<alpha>_el a)) \<and> finite (-B)"
  and "\<And>a. \<not>dependvar (\<phi>_off a) M 0"
  and "\<And>a. \<not>dependvar (\<phi>_on a) M 0"
  and invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
  and locking: "\<And>s. locked M B s = (\<forall> a \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e)"
  and exclusive: "\<And>s a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "s \<in> \<lbrakk>nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (Acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0))))))\<rbrakk> M e
    = ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
  apply (simp add: assms del: Diamond.simps occurssimps locking)
  apply (subst lemma50)
  apply (simp add: assms)
  apply (simp add: assms)
  apply (subst notdependshiftdown)
  apply (simp add: assms)
proof
  assume "\<exists>S'. S' \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'"
  then obtain S' where assum1: "S' \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el a \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'" by auto
  let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)}"
  have "\<forall>s \<in> ?S'. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)))"
    apply (rule ballI)+
  proof
    fix s a
    assume assum2: "s \<in> ?S'"
    hence "s \<in> S'" by auto
    moreover assume "a \<in> - B"
    moreover assume "s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
    ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el a \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'))" using assum1 by auto
    then obtain p s' where validpath: "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' a'. a' \<in> \<alpha>_el a \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'))" using assum1 by presburger
    moreover have "enabled M s' \<alpha>\<^sub>e \<Longrightarrow> False" using assum2 validpath by auto
    moreover {
      assume s'inS' : "s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e"
      moreover have "s' \<in> insert s (set (map target p))" using validpath by (subst sourcetargetfin[where ?s'=s']; auto)
      ultimately have "occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)" by auto
      moreover have "\<nexists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" 
      proof
        assume "\<exists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)"
        then obtain p' s'' where "validfinpath M s' p' s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" by auto
        hence "validfinpath M s (p @ p') s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin (p @ p')) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" using validpath addpathsnotoccurs by metis
        thus False using assum2 by blast
      qed
      ultimately have "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)" using validpath s'inS' by auto
    }
    moreover {
      assume "\<exists>s'' a'. a' \<in> \<alpha>_el a \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'"
      then obtain a' s'' where s''inS': "a' \<in> \<alpha>_el a \<and> a' \<notin> \<alpha>\<^sub>f \<and> (s', a', s'') \<in> transition M \<and> s'' \<in> S'" by auto
      hence "validfinpath M s' [(s', a', s'')] s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin ([(s', a', s'')])) \<and> occurs (\<alpha>_el a) (fin (p @ [(s', a', s'')]))" by auto
      hence validaddpath : "validfinpath M s (p @ [(s', a', s'')]) s'' \<and>  \<not> occurs \<alpha>\<^sub>f (fin (p @ [(s', a', s'')])) \<and> occurs (\<alpha>_el a) (fin (p @ [(s', a', s'')]))" using validpath validfinpathsplit addpathsnotoccurs by metis 
      moreover have "\<nexists>p s'. validfinpath M s'' p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)" 
      proof
        assume "\<exists>p s'. validfinpath M s'' p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)"
        then obtain p' s''' where "validfinpath M s'' p' s''' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s''' \<or> enabled M s''' \<alpha>\<^sub>e)" by auto
        hence "validfinpath M s ((p @ [(s', a', s'')]) @ p') s''' \<and> \<not> occurs \<alpha>\<^sub>f (fin ((p @ [(s', a', s'')]) @ p')) \<and> (locked M B s''' \<or> enabled M s''' \<alpha>\<^sub>e)" using validaddpath addpathsnotoccurs by metis
        thus False using assum2 by blast
      qed
      ultimately have "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> occurs (\<alpha>_el a) (fin p)" using s''inS' by blast
    }
    ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p))" by blast
  qed
  moreover have "\<And>s. s \<in> ?S' \<Longrightarrow> \<not>locked M B s" 
    apply (subgoal_tac "validfinpath M s [] s \<and> \<not> occurs \<alpha>\<^sub>f (fin [])")
    apply blast
    apply simp
    done
  ultimately have "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
    apply (subst constructfairpath)
    using exclusive persistent assms(1) apply blast+
    using locking apply meson
    using persistent assms(1) apply blast+
    done
  hence "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)" using invarinf by blast
  thus "((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))" using assum1 by blast
next
  let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))}"
  assume "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))"
  hence "s \<in> ?S'" by simp
  moreover have "?S' \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S')))})"
    apply (rule subsetI INT_I CollectI impI)+
  proof-
    fix s a
    assume assum1: "s \<in> ?S'"
    assume assum2 : "a \<in> -B"
    assume assum3 : "s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e" 
    show "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S'))"
    proof-
      have "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))" using assum1 by auto
      moreover {
        assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)"
        hence "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)" by auto
        moreover {
          assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
          then obtain p s' where assum4: "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'" by auto
          moreover have "occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)"
            apply (rule ccontr)
            apply (subgoal_tac "s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e")
            using locking persistent assum2 assum3 assum4 apply blast+
            done
          ultimately have assum4: "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p))" by auto
(*staat dit al ergens anders*)
          moreover {
            assume "occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)"
            hence "s \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists> n \<in> indicespath (fin p). target (ind n (fin p)) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)" using occursstatealternative by metis
            hence "s \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists> n < length p. target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)" by simp
            moreover have "s \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<Longrightarrow> validfinpath M s [] s \<and> \<not> occurs \<alpha>\<^sub>f (fin [])  \<and> s \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e" using assum1 by simp
            moreover {
              assume "\<exists> n < length p. target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e"
              then obtain n where "n < length p \<and> target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e" by auto
              hence "validfinpath M (target (p!n)) (drop (Suc n) p) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (drop (Suc n) p)) \<and> locked M B s' \<and> validfinpath M s (take (Suc n) p) (target (p!n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (take (Suc n) p)) \<and> target (p!n) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e" 
                using assum4 validfinsubpathtargetright notoccursfinright notoccursfinleft validfinsubpathtarget by metis
              hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p)  \<and> s' \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e" by auto
            }
            ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p)  \<and> s' \<in> ?S' \<inter> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e" by blast
          }
          moreover {
            assume "occurs (\<alpha>_el a) (fin p)"
            then obtain n where "n < length p \<and> action (p!n) \<in> \<alpha>_el a" using occursfinalternative by blast
            hence "validfinpath M (target (p!n)) (drop (Suc n) p) s' \<and> \<not>occurs \<alpha>\<^sub>f (fin (drop (Suc n) p)) \<and> locked M B s' \<and> validfinpath M s (take n p) (source (p!n)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (take n p)) \<and> (source (p!n), action (p!n), target (p!n)) \<in> transition M \<and> action (p!n) \<in> \<alpha>_el a \<and> action (p!n) \<notin> \<alpha>\<^sub>f" 
              using assum4 validfinsubpath validfinsubpathtargetright notoccursfinright notoccursfinleft occursfinalternative ithtransitionfinpath splittransition by metis
            hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p)  \<and> (\<exists>act s''. (s', act, s'') \<in> transition M \<and> act \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> s'' \<in> ?S')" by blast
          }
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> ((s' \<in> ?S' \<inter> (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)) \<or> (\<exists>act s''. (s', act, s'') \<in> transition M \<and> act \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> s'' \<in> ?S'))" 
          by meson
        }
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S'))" by blast
      }
      moreover {
        assume "\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)"
        then obtain p where predP: "validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))" using invarinf by auto
        moreover from this have "source (p 0) = s \<and> suffix 0 p = p" by (simp add: validinfpath_def)
        ultimately have validinfpath: "validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> (occurs (\<alpha>_el a) (inf p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (inf p))" using assum2 assum3 by metis
        then obtain i where sourceoraction : "source (p i) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> action (p i) \<in> \<alpha>_el a" using infpathoccursoroccursstate by metis
        have "\<And>j. source (p j) \<in> ?S'"
        proof-
          fix j
          have "validinfpath M (source (p j)) (suffix j p) \<and> \<not> occurs \<alpha>\<^sub>f (inf (suffix j p)) \<and> P (source (p j)) (inf (suffix j p))"
          proof-
            have "(\<forall>a \<in> -B. ((\<forall>k. (source ((suffix j p) k)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix k (suffix j p))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source ((suffix j p) k)) (inf (suffix k (suffix j p)))))))" using predP by simp
            moreover have "validinfpath M (source (p j)) (suffix j p) \<and>  \<not> occurs \<alpha>\<^sub>f (inf (suffix j p))" using predP by auto
            ultimately show ?thesis using invarinf by metis
          qed
          thus "source (p j) \<in> ?S'" by blast
        qed
        moreover have "target (p i) = source (p (Suc i))" using predP by (simp add: validinfpath_def)
        ultimately have "source (p i) \<in> ?S' \<and> target (p i) \<in> ?S'" by auto
        moreover have "validfinpath M s (prefix i p) (source (p i)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (prefix i p)) \<and> action (p i) \<notin> \<alpha>\<^sub>f" using validinfpath validinfsubpath by auto
        moreover have "(source (p i), action (p i), target (p i)) \<in> transition M" using validinfpath splittransition validinfpath_def by metis
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S'))" using sourceoraction by blast
      }
      ultimately show ?thesis by blast
    qed
  qed
  ultimately show "\<exists>x. x \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> x \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a - \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> x)))}) \<and> s \<in> x" by blast
qed

(*use both of these in previous lemma*)
lemma predPsubpathinf :
  assumes invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  shows "validfinpath M s p s' \<and> validinfpath M s' p' \<and> P s (inf (conc p p')) \<Longrightarrow> P s' (inf p')"
proof-
  assume assum1 : "validfinpath M s p s' \<and> validinfpath M s' p' \<and> P s (inf (conc p p'))"
  hence "validinfpath M s (conc p p') \<and> P s (inf (conc p p'))" by auto
  hence "\<forall>a \<in> -B. ((\<forall>i. (source ((conc p p') (i + length p))) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix (i + length p) (conc p p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source ((conc p p') (i + length p))) (inf (suffix (i + length p) (conc p p'))))))" using invarinf by blast
  hence "\<forall>a \<in> -B. ((\<forall>i. (source (p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' i)) (inf (suffix i p')))))" by auto
  thus ?thesis using assum1 invarinf by metis  
qed

lemma predPsuperpathinf :
  assumes invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "validfinpath M s p s' \<and> validinfpath M s' p' \<and> P s' (inf p') \<Longrightarrow> P s (inf (conc p p'))"
proof-
  assume assum1 : "validfinpath M s p s' \<and> validinfpath M s' p' \<and> P s' (inf p')"
  hence predPentirepath: "\<forall>a \<in> -B. ((\<forall>i. (source (p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' i)) (inf (suffix i p')))))" using invarinf by blast
  have "\<forall>a \<in> -B. ((\<forall>i. (source (conc p p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i (conc p p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (conc p p' i)) (inf (suffix i (conc p p'))))))"
    apply (rule ballI allI)+
  proof
    fix a i
    assume assum2 : "a \<in> -B"
    assume assum3 : "source (conc p p' i) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
    {
      assume assum4 : "i < length p"
      hence "validfinpath M (source (p ! i)) (drop i p) s' \<and> source (p' 0) = s'" using assum1 validfinsubpathright validinfpath_def by metis
      moreover have nonempty : "drop i p \<noteq> []" using assum4 by auto
      ultimately have "validfinpath M (source (p ! i)) (drop i p) (laststate (drop i p)) \<and> source (p' 0) = laststate (drop i p)" using validfinpathlaststate by metis
      moreover from this have "\<not>occurs (\<alpha>_el a) (fin (drop i p)) \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p!i)) (fin (drop i p)) \<Longrightarrow> laststate (drop i p) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e" using assum2 assum3 assum4 conc_fst persistent by metis
      ultimately have "occurs (\<alpha>_el a) (fin (drop i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p!i)) (fin (drop i p)) \<or> occurs (\<alpha>_el a) (inf (suffix 0 p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (laststate (drop i p)) (inf (suffix 0 p'))" using assum2 predPentirepath by metis
      hence "occurs (\<alpha>_el a) (fin (drop i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p!i)) (fin (drop i p)) \<or> occurs (\<alpha>_el a) (inf p') \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (laststate (drop i p)) (inf p')" by auto
      hence "occurs (\<alpha>_el a) (inf (conc (drop i p) p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p!i)) (inf (conc (drop i p) p'))" using extendfinpath.simps(2) nonempty occursstateleft occursleft occursright occursstateright by metis
      hence "occurs (\<alpha>_el a) (inf (suffix i (conc p p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (conc p p' i)) (inf (suffix i (conc p p')))" using assum4 by auto  
    }
    moreover {
      assume assum4 : "i \<ge> length p"
      hence "conc p p' i = p' (i - length p)" by auto
      hence "occurs (\<alpha>_el a) (inf (suffix (i - length p) p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' (i - length p))) (inf (suffix (i - length p) p'))" using assum2 assum3 predPentirepath by auto
      hence "occurs (\<alpha>_el a) (inf (suffix i (conc p p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (conc p p' i)) (inf (suffix i (conc p p')))" using assum4 by auto
    }
    moreover have "i < length p \<or> i \<ge> length p" by auto
    ultimately show "occurs (\<alpha>_el a) (inf (suffix i (conc p p'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (conc p p' i)) (inf (suffix i (conc p p')))" by blast
  qed
  moreover have "validinfpath M s (conc p p')" using assum1 by auto
  ultimately show ?thesis using invarinf by auto
qed

lemma predPsubpathsuperpathfin :
  assumes invarfin: "\<And>p s s'. validfinpath M s p s' \<Longrightarrow> locked M B s' = P s (fin p)"
  shows "validfinpath M s p s' \<and> validfinpath M s' p' s'' \<Longrightarrow> P s' (fin p') = P s (fin (p @ p'))"
  using invarfin validfinpathsplit by meson

lemma predPsubpathsuperpathinf :
  assumes invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "validfinpath M s p s' \<and> validinfpath M s' p' \<Longrightarrow> P s' (inf p') = P s (inf (conc p p'))"
  apply (rule iffI)
  apply (rule predPsuperpathinf [where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el and ?e=e and ?B=B and ?M=M and ?p=p and ?s=s and ?s'=s'])
  prefer 4
  apply (rule predPsubpathinf [where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el and ?e=e and ?B=B and ?M=M and ?p=p and ?s=s])
  using invarinf persistent apply blast+
  done

lemma predPsubpathsuperpath :
  assumes invarfin: "\<And>p s s'. validfinpath M s p s' \<Longrightarrow> P s (fin p) = locked M B s'"
  and invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  shows "validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s' p' = P s (extendfinpath p p')"
proof-
  assume assum1: "validfinpath M s p s' \<and> validpath M s' p'"
  {
    fix fp
    assume assum2: "p' = fin fp"
    then obtain s'' where "validfinpath M s p s' \<and> validfinpath M s' fp s''" using assum1 by auto
    hence "P s' (fin fp) = P s (fin (p @ fp))" by (subst predPsubpathsuperpathfin[where ?B=B and ?s''=s'']; auto simp: invarfin)
    hence "P s' p' = P s (extendfinpath p p')" using assum2 by simp
  }
  moreover {
    fix ip
    assume assum2: "p' = inf ip"
    hence "validfinpath M s p s' \<and> validinfpath M s' ip" using assum1 by auto
    hence "P s' (inf ip) = P s (inf (conc p ip))" using invarinf persistent by (subst predPsubpathsuperpathinf[where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el and ?e=e and ?B=B]; blast)
    hence "P s' p' = P s (extendfinpath p p')" using assum2 by simp
  }
  ultimately show ?thesis by (cases p')
qed

lemma notlocked : "s \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> locked M B s'} \<and> validfinpath M s p s' \<Longrightarrow> s' \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> locked M B s'}"
  using validfinpathsplit by (simp; meson)

lemma feasible : 
  assumes invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> P s (inf p) =  ((\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and locking: "\<And>s. locked M B s = (\<forall> a \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e)"
  and exclusive: "\<And>s a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and feasiblesub: "\<And>a s. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)))"
  and "finite (-B)"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> P s (inf p))"
proof-
  let ?S' = "{s. \<nexists>p s'. validfinpath M s p s' \<and> locked M B s'}"
  have "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> \<not>occurs {} (inf p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))"
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
    fix s'' a
    assume assum1: "s'' \<in> ?S'"
    assume "a \<in> -B"
    moreover assume "s'' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
    ultimately obtain p s' where "validfinpath M s'' p s' \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s'' (fin p))" using feasiblesub by blast
    moreover from this have "s' \<in> ?S'" using assum1 by (subst notlocked [where ?s=s'' and ?p=p]; auto)
    ultimately show "\<exists>p s'. validfinpath M s'' p s' \<and> s' \<in> ?S' \<and> \<not> occurs {} (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s'' (fin p))" by (simp; blast)
  qed
  hence "s \<in> ?S' \<Longrightarrow> \<exists>p. validinfpath M s p \<and> P s (inf p)" using invarinf by blast
  thus ?thesis by auto
qed

theorem theorem24 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>a. finite (\<alpha>_el a)) \<and> finite (-B)"
  and "\<And>a. \<not>dependvar (\<phi>_off a) M 0"
  and "\<And>a. \<not>dependvar (\<phi>_on a) M 0"
  and invarfin: "\<And>p s s'. validfinpath M s p s' \<Longrightarrow>  P s (fin p) = locked M B s'"
  and invarinf: "\<And>p s. validinfpath M s p \<Longrightarrow> P s (inf p) =  ((\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and locking: "\<And>s. locked M B s = (\<forall> a \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e)"
  and exclusive: "\<And>s a. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e " 
  and persistent: "\<And>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<Longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and reachable: "\<And>a s. a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<Longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)))" 
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (Acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p)"
  apply (subst negformula)
  apply (subst Diamondmatch)
  apply (subst theorem24_subformula; (rule assms; auto)?)
  apply (subst splitviolating_predicate)
proof-
  fix p p' s'
  show "validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s' p' = P s (extendfinpath p p')"
    by (subst predPsubpathsuperpath [where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el and ?e=e and ?B=B and ?M=M and ?s=s and ?p = p]; (rule assms)?; auto)
next
  have "\<And>s. (\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p) =
    ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
    \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
    apply (subst freeuntiloccurrenceprogressing_lockedenabled_pred) 
    apply (subst feasible [where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el])
    using invarinf locking exclusive persistent reachable assms(1) apply blast+
    using invarinf persistent apply (subst predPsubpathsuperpathinf[where ?\<phi>_on=\<phi>_on and ?\<phi>_off=\<phi>_off and ?\<alpha>_el=\<alpha>_el and ?e=e and ?B=B]; blast)
    using invarfin apply blast+
    done
  thus "(\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> ((\<exists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s' (inf p)))) =
      (\<nexists>p p' s'. match \<rho> p \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> P s' p')" by blast
qed

corollary corollary25 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (box a ff) (var 0))) (Diamond (Acts ({a} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> WFA M B s p)"
  apply (rule theorem24)
  apply (simp add: assms notoccursnotdepends)+
  apply (simp add: WFAinvarfin)
  apply (simp only: WFAinvarinf)
  apply (simp add: locked_def; blast)
  apply simp
proof-
  fix a s
  assume "a \<in> - B \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e"
  then obtain s' where "(s, a, s') \<in> transition M" by auto
  hence "validfinpath M s [(s, a, s')] s' \<and> occurs {a} (fin [(s, a, s')])" by auto
  thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a} (fin p) \<or> occursstate (\<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e) s (fin p))" by blast
next
  fix s p s' a
  assume "a \<in> - B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e \<and> \<not> occursstate (\<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e) s (fin p) \<and> \<not> occurs {a} (fin p)"
  hence "s' \<notin> \<lbrakk>shiftdown (box a ff) 0\<rbrakk> M e" using notoccursendpath by metis
  thus "s' \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e" by simp
qed

lemma lockedphion_WHFA: "finite (-B) \<Longrightarrow> locked M B s = (\<forall>a\<in>- B. s \<notin> \<lbrakk>shiftdown (Diamond (Star (Acts (- B))) (diamond a tt)) 0\<rbrakk> M e)"
  apply (simp only: shiftdownDiamond shiftdownBox shiftdown.simps)
  apply (simp only: Diamondreachable)
proof-
  have "locked M B s = WHFA M B s (fin [])" by (simp only: WHFAempty)
  thus "locked M B s = (\<forall>a\<in>- B. a \<notin> reachableactions M B s)" by (auto simp: WHFA_def perpetuallyreachable_def)
qed

corollary corollary26 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (Diamond (Star (Acts (-B))) (diamond a tt))) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' (Box (Star (Acts (-B))) (box a ff)) (var 0))) (Diamond (Acts ({a} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> WHFA M B s p)"
  apply (rule theorem24)
  apply (simp add: assms notoccursnotdepends)+
  apply (simp add: WHFAinvarfin)
  apply (simp only: WHFAinvarinf assms)
  apply (simp only: lockedphion_WHFA assms; simp)
  apply (simp only: shiftdownDiamond shiftdownBox shiftdown.simps)
  using Boxnotreachable Diamondreachable assms apply meson
proof-
  fix s p s' a
  assume "a \<in> - B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (Diamond (Star (Acts (- B))) (diamond a tt)) 0\<rbrakk> M e \<and> \<not> occursstate (\<lbrakk>shiftdown (Box (Star (Acts (- B))) (box a ff)) 0\<rbrakk> M e) s (fin p) \<and> \<not> occurs {a} (fin p)"
  hence "s' \<notin> \<lbrakk>shiftdown (Box (Star (Acts (- B))) (box a ff)) 0\<rbrakk> M e" using notoccursendpath by meson
  hence "s' \<in> \<lbrakk>neg (Box (Star (Acts (- B))) (box a ff))\<rbrakk> M e" by simp
  moreover have "\<lbrakk>neg (box a ff)\<rbrakk> M e = \<lbrakk>diamond a tt\<rbrakk> M e" by auto
  ultimately have "s' \<in> \<lbrakk>Diamond (Star (Acts (- B))) (diamond a tt)\<rbrakk> M e" using negBox Diamond_eq by metis
  thus "s' \<in> \<lbrakk>shiftdown (Diamond (Star (Acts (- B))) (diamond a tt)) 0\<rbrakk> M e" by simp
next
  fix a s
  assume "a \<in> - B \<and> s \<in> \<lbrakk>shiftdown (Diamond (Star (Acts (- B))) (diamond a tt)) 0\<rbrakk> M e"
  hence "s \<in> \<lbrakk>Diamond (Star (Acts (- B))) (diamond a tt)\<rbrakk> M e" by simp
  hence "a \<in> reachableactions M B s" by (simp only: Diamondreachable assms)
  then obtain p s' s'' where "validfinpath M s p s' \<and> (s', a, s'') \<in> transition M" by (auto simp: reachableactionsdef)
  hence "validfinpath M s (p@[(s', a, s'')]) s'' \<and> occurs {a} (fin (p@[(s', a, s'')]))" by simp
  thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a} (fin p) \<or> occursstate (\<lbrakk>shiftdown (Box (Star (Acts (- B))) (box a ff)) 0\<rbrakk> M e) s (fin p))" by blast
qed

corollary corollary27 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B) \<and> (\<forall>a. finite {a'. \<not> con a a'})"
  and "concurrency M con"
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Diamond (Acts ({a'. \<not> con a a'} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> JA M con B s p)"
proof-
  have "\<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (Diamond (Acts \<alpha>\<^sub>e) tt) (Diamond (Acts ({a'. \<not> con a a'} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
    \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' ff (var 0))) (Diamond (Acts ({a'. \<not> con a a'} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e"
    by (simp add: assms(1) Diamond_eq)
  moreover have "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (diamond a tt)) (Diamond (Star (Acts (-\<alpha>\<^sub>f))) (or (or (Diamond (Acts \<alpha>\<^sub>e) tt) (and' ff (var 0))) (Diamond (Acts ({a'. \<not> con a a'} - \<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> JA M con B s p)"
  apply (rule theorem24)
  apply (simp add: assms notoccursnotdepends)+
  apply (simp add: JAinvarfin assms)
  apply (simp only: JAinvarinf)
  apply (simp add: locked_def; blast)
  apply simp
  proof-
    fix a s
    assume "a \<in> -B \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e"
    then obtain s' where "(s, a, s') \<in> transition M" by auto
    moreover have "\<not> con a a" using assms(2) by (simp add: concurrency_def)
    ultimately have "validfinpath M s [(s, a, s')] s' \<and> occurs {a'. \<not> con a a'} (fin [(s, a, s')])" by auto
    thus "\<exists>p s'. validfinpath M s p s' \<and> (occurs {a'. \<not> con a a'} (fin p) \<or> occursstate (\<lbrakk>shiftdown ff 0\<rbrakk> M e) s (fin p))" by blast
  next
    fix s p s' a
    have "validfinpath M s p s' \<longrightarrow> enabledactions M s \<inter> preimagerelation con (alloccurringactions (fin p)) \<subseteq> enabledactions M s'" using assms(2) by (auto simp: concurrency_def)
    moreover assume "a \<in> - B \<and> validfinpath M s p s' \<and> s \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e \<and> \<not> occursstate (\<lbrakk>shiftdown ff 0\<rbrakk> M e) s (fin p) \<and> \<not> occurs {a'. \<not> con a a'} (fin p)"
    ultimately have "a \<in> enabledactions M s'" by auto
    thus "s' \<in> \<lbrakk>shiftdown (diamond a tt) 0\<rbrakk> M e" by simp
  qed
  ultimately show ?thesis by blast
qed

lemma Diamondor : "\<lbrakk>Diamond R (or f g)\<rbrakk> M e = \<lbrakk>or (Diamond R f) (Diamond R g)\<rbrakk> M e"
proof-
  have "\<And>s. s \<in> \<lbrakk>Diamond R (or f g)\<rbrakk> M e = (s \<in> \<lbrakk>or (Diamond R f) (Diamond R g)\<rbrakk> M e)" by (auto simp: Diamondmatch)
  thus ?thesis by auto
qed

lemma freeenabledpath : 
  assumes "finite (- \<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e"
  shows "s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) (or (Diamond (Acts \<alpha>\<^sub>e) tt) f)\<rbrakk> M e =
    (s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) f\<rbrakk> M e \<or> 
       (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e))" 
  apply (subst Diamondor)
proof-
  have "s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) (Diamond (Acts \<alpha>\<^sub>e) tt)\<rbrakk> M e = 
    (\<exists>p s'. validfinpath M s p s' \<and> match (Star (Acts (- \<alpha>\<^sub>f))) p \<and> s' \<in> \<lbrakk>Diamond (Acts \<alpha>\<^sub>e) tt\<rbrakk> M e)" by (rule Diamondmatch)
  moreover have "... = (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)" by (subst Diamond_enabled matchstaract; simp add: assms)+
  ultimately show "(s \<in> \<lbrakk>formula.or (Diamond (Star (Acts (- \<alpha>\<^sub>f))) (Diamond (Acts \<alpha>\<^sub>e) tt)) (Diamond (Star (Acts (- \<alpha>\<^sub>f))) f)\<rbrakk> M e) = 
    (s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) f\<rbrakk> M e \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e))" unfolding formulasemantics.simps by blast
qed

lemma SFAformula : 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  and feasible: "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p \<and> SFA M B s (inf p))"
  and subformula: "\<And>s. s \<in> \<lbrakk>Diamond (Star (Acts (- \<alpha>\<^sub>f))) f\<rbrakk> M e =
        ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')
        \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> SFA M B s (inf p)))" 
  shows "s \<in> \<lbrakk>neg (Diamond (Times \<rho> (Star (Acts (- \<alpha>\<^sub>f)))) (or (Diamond (Acts \<alpha>\<^sub>e) tt ) f))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> SFA M B s p)"
  apply (subst negformula)
  unfolding Diamond.simps(5) apply (subst Diamondmatch)
  apply (subst splitviolating_predicate)
  apply (simp only: SFA_extendpath)
  apply (subst freeenabledpath)
  apply (simp add: assms)
  apply (subst subformula)
proof-
  have "\<And>s. (\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> SFA M B s p) =
    ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
    \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> SFA M B s (inf p)))"
    apply (rule freeuntiloccurrenceprogressing_lockedenabled_pred) 
    apply (rule feasible)
    apply (auto simp: SFA_extendpath)
    apply (simp only: SFAinvarfin)
    done
  thus "(\<nexists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> (((\<exists>p s'a. validfinpath M s' p s'a \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'a) \<or> (\<exists>p. validinfpath M s' p \<and> \<not> occurs \<alpha>\<^sub>f (path.inf p) \<and> SFA M B s' (path.inf p))) \<or> (\<exists>p s'a. validfinpath M s' p s'a \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s'a \<alpha>\<^sub>e))) = 
    (\<nexists>p p' s'. match \<rho> p \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> SFA M B s' p')" by blast
qed

end