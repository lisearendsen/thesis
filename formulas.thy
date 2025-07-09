theory formulas
imports paths Main
begin

lemma shiftdownnewenv_eq_newenvshiftdown [simp] : "shiftdownenv (newenvironment e S') (Suc i) = newenvironment (shiftdownenv e i) S'"
  apply (rule)
  apply (induct_tac x)
  apply (simp_all add: shiftdownenv_def)
  done

lemma shiftdownnewenvzero_eq_newenv [simp] : "shiftdownenv (newenvironment e S') 0 = e"
  apply (rule)
  apply (induct_tac x; simp add: shiftdownenv_def)
  done

lemma switchnewenvironmentshiftdown : "\<lbrakk>shiftdown f (Suc i)\<rbrakk> M (newenvironment (shiftdownenv e i) S') = 
  \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))"
  by simp

(*lemma dependvarX : "dependvari (var X) M X" by (auto simp: dependvari_def)*)

(*lemma notdependvarXshiftdown : "\<not> dependvari (var X) M i \<longrightarrow> \<lbrakk>shiftdown (var X) i\<rbrakk> M (shiftdownenv e i) = \<lbrakk>var X\<rbrakk> M e"
  apply simp
  apply (rule; intro impI)
proof-
  assume "X \<le> i"
  moreover assume "\<not> dependvari (var X) M i"
  ultimately have "X < i" using dependvarX le_neq_implies_less by blast
  thus "shiftdownenv e i X = e X" by (simp add: shiftdownenv_def)
next
  assume "\<not> X \<le> i"
  hence "(X - Suc 0) \<ge> i \<and> Suc (X - Suc 0) = X" by auto
  thus "shiftdownenv e i (X - Suc 0) = e X" by (simp add: shiftdownenv_def)
qed*)

(*lemma shiftdownlemma [simp] : "\<not> dependvari f M i \<longrightarrow> \<lbrakk>shiftdown f i\<rbrakk> M (shiftdownenv e i) = \<lbrakk>f\<rbrakk> M e"
  apply (induct f arbitrary: e i)
  prefer 3 apply (rule notdependvarXshiftdown)
  apply (simp_all add: shiftdownenv_def)
  apply blast
  apply (rule impI)
  apply (subst switchnewenvironmentshiftdown)
  prefer 2 
  apply (rule impI) 
  apply (subst switchnewenvironmentshiftdown)
proof-
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Inter> {S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S'}" by auto
next
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by auto
qed*)

lemma shiftdownlemma [simp] : "\<not> occursvari f i \<longrightarrow> \<lbrakk>shiftdown f i\<rbrakk> M (shiftdownenv e i) = \<lbrakk>f\<rbrakk> M e"
  apply (induct f arbitrary: e i; simp add: shiftdownenv_def)
  apply (arith)
  apply (rule impI)
  apply (subst switchnewenvironmentshiftdown)
  prefer 2 
  apply (rule impI) 
  apply (subst switchnewenvironmentshiftdown)
proof-
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Inter> {S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S'}" by auto
next
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by auto
qed

definition envrepeati :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"envrepeati e i \<equiv> conc (prefix (Suc i) e) (suffix i e)"

lemma envrepeatidef :  "envrepeati e i = (\<lambda>j. if j > Suc i then e (j - Suc 0) else (if j \<le> i then e j else e i))"
proof
  fix j
  {
    assume assum1 : "Suc i < j"
    hence "\<not>j < length (prefix (Suc i) e)" by simp
    hence "conc (prefix (Suc i) e) (suffix i e) j = suffix i e (j - length (prefix (Suc i) e))" using conc_snd by metis
    hence "conc (prefix (Suc i) e) (suffix i e) j = e (j - Suc 0)" using assum1 by simp
  }
  moreover {
    assume "j \<le> i"
    hence "j < length (prefix (Suc i) e)" by auto
    hence "conc (prefix (Suc i) e) (suffix i e) j = e j" using prefix_suffix conc_fst by metis
  }
  moreover {
    assume "\<not>Suc i < j"
    moreover assume "\<not>j \<le> i"
    ultimately have "j = Suc i" by auto
    hence "conc (prefix (Suc i) e) (suffix i e) j = e i" by auto
  }
  ultimately show "envrepeati e i j = (if Suc i < j then e (j - Suc 0) else if j \<le> i then e j else e i)" using envrepeati_def by metis
qed

lemma newenvenvrepeatswitch : "newenvironment (envrepeati e i) S' = envrepeati (newenvironment e S') (Suc i)"
  apply (rule)
  apply (induct_tac x; simp add: envrepeati_def)
proof-
  fix n
  show "conc (prefix i e) (newenvironment (suffix i e) (e i)) n = conc (prefix i e) (newenvironment (suffix (Suc i) (newenvironment e S')) (e i)) n" by (induct n; simp)
 qed

lemma shiftdownenvrepeat : "\<lbrakk>shiftdown f i\<rbrakk> M e = \<lbrakk>f\<rbrakk> M (envrepeati e i)"
  apply (induct f arbitrary: e i; simp add: shiftdownenv_def newenvenvrepeatswitch)
  apply (simp add: envrepeatidef)
  apply (intro impI)
  apply (subgoal_tac "x = Suc i"; auto)
  done

lemma shiftdownnewenv : "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>shiftdown f 0\<rbrakk> M e "
  apply (subgoal_tac "envrepeati e 0 = newenvironment e (e 0)")
  apply (simp add: shiftdownenvrepeat)
  apply rule
  apply (induct_tac x; simp add: envrepeati_def)
  done

lemma notdependshiftdown : "\<not>dependvari f M 0 \<Longrightarrow> \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>shiftdown f 0\<rbrakk> M e"
proof- 
  assume "\<not>dependvari f M 0"
  hence "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>f\<rbrakk> M (newenvironment e (e 0))(0 := S')" using dependvari_def by metis
  moreover have "\<lbrakk>f\<rbrakk> M (newenvironment e (e 0)) = \<lbrakk>shiftdown f 0\<rbrakk> M e" using shiftdownnewenv by metis
  moreover have "(newenvironment e (e 0))(0 := S') = newenvironment e S'" by simp
  ultimately show ?thesis by (simp add: shiftdownenvrepeat)
qed

(*should this not be in semantics*)
(*lemma shiftdowncoro : "\<not>occursvari f 0 \<longrightarrow> \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>shiftdown f 0\<rbrakk> M e" 
  using shiftdownlemma shiftdownnewenvzero_eq_newenv by metis*)

(*lemma shiftdowncoro : "\<not>dependvari f M 0 \<longrightarrow> \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>shiftdown f 0\<rbrakk> M e" 
  using shiftdownlemma shiftdownnewenvzero_eq_newenv by meti*)

lemma targetpath [simp]: 
"validfinpath M s p s' \<longrightarrow> s' \<in> insert s (set (map target p))"
  by (induct p arbitrary : s; simp)

lemma prop40rtl :
  assumes "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)"
  and "\<not> dependvari f M 0"
  and "\<not> dependvari g M 0"
  and "finite A"
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e)"
  apply (simp add: assms(4) del: Diamond.simps)
proof-
  from assms(1) obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by auto
  show "\<forall>S'. formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S' \<longrightarrow> s \<in> S'"
    apply (rule allI)
    apply (rule impI)
  proof-
  fix S'
  assume assum2 : "formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S'"
  have inS' : "(validfinpath M s p s' \<and> (action ` set p \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> S') \<longrightarrow> s \<in> S'"
    apply (induct p arbitrary : s; simp)
    apply (rule impI)
  proof-
    fix t p s
    assume assum3 : "(\<And>s. validfinpath M s p s' \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S')"
    assume assum4 : "s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S'"
    hence "target t \<in> S'" using assum3 by auto
    hence "(source t, action t, target t) \<in> transition M \<and> target t \<in> S'" using assum4 splittransition by metis
    hence c1 : "source t \<in> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assum4 by blast
    have "source t \<in> formulasemantics (shiftdown g 0) M e" using assum4 by auto
    hence c2 : "source t \<in> formulasemantics g M (newenvironment e S')" using notdependshiftdown assms(3) by metis
    show "source t \<in> S'" using c1 c2 assum2 by auto
  qed
  have "s' \<in> insert s (set (map target p))" using targetpath assum1 by metis
  hence "s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> (formulasemantics (shiftdown f 0) M e)" using assum1 by auto
  hence "s' \<in> formulasemantics g M (newenvironment e S') \<and> s' \<in> formulasemantics f M (newenvironment e S')" using assms(2) assms(3) notdependshiftdown by metis
  hence "s' \<in> S'" using assum2 by auto
  thus "s \<in> S'" using assum1 inS' by auto
qed
qed

lemma prop40ltrinbetween :
  assumes "\<not>dependvari f M 0"
  and "\<not>dependvari g M 0"
  and "finite A"
  shows "s \<in> ((transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)^^n){} \<longrightarrow>
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> A)
     \<and> s \<in> (formulasemantics (shiftdown g 0) M e)
     \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  apply (induct n arbitrary : s)
  apply (simp)
proof
  fix n s
  let ?f = "and' g (or f (Diamond (acts A) (var 0)))"
  let ?S' = "(transformer ?f M e ^^ n) {}"
  assume assum1 : "\<And>s. s \<in> ?S'
    \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  let ?S'' = "(transformer ?f M e ^^ Suc n) {}"
  assume assum2 : "s \<in> ?S''"
  hence splitand : "s \<in> \<lbrakk>g\<rbrakk> M (newenvironment e ?S') 
    \<and> (s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'))" by (simp add: transformer_def assms(3) del: Diamond.simps)
  hence ing : "s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e" using notdependshiftdown assms by metis
  from splitand have "s \<in> formulasemantics f M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S')" by auto
  moreover {
    assume assum3 : "s \<in> formulasemantics f M (newenvironment e ?S')"
    from assum3 have "s \<in> (formulasemantics (shiftdown f 0) M e)" by (metis assms(1) notdependshiftdown)
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set [] \<subseteq> A) \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set []) \<subseteq> (formulasemantics (shiftdown g 0) M e)" using ing by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set p) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  moreover {
    assume "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'"
    from this obtain s' act where assum3 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'" by auto
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" using assum1 by auto
    from this obtain p s'' where tail : "validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" by auto
    let ?p = "(s, act, s') # p"
    have "source (s, act, s') = s \<and> (s, act, s') \<in> transition M \<and> validfinpath M (target (s, act, s')) p s''" using assum3 tail by (simp)
    hence "validfinpath M s ?p s''" by auto
    hence "validfinpath M s ?p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set ?p \<subseteq> A) \<and> 
      s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set ?p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using assum3 ing tail by (simp)
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A 
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using splitand by blast
qed

lemma monotonicityformula40 : 
  assumes  "\<not>dependvari f M 0"
  and "\<not>dependvari g M 0"
  and "finite A"
  shows "mono (transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)"
  apply (simp add: assms(3))
proof-
  have "notdependalloccursposnegi (and' g (or f (Diamondlist (SOME listA. set listA = A) (var 0)))) M 0 True"
    apply (rule someI2_ex)
    apply (simp add: finite_list assms(3))
  proof-
    fix listA
    have "notdependalloccursposnegi (Diamondlist listA (var 0)) M 0 True" by (induct listA; simp)
    thus "notdependalloccursposnegi (and' g (formula.or f (Diamondlist listA (var 0)))) M 0 True" using assms notdepends by auto
  qed
  thus "mono (transformer (and' g (or f (Diamondlist (SOME listA. set listA = A) (var 0)))) M e)" using monotonicitynotdependcoro(1) by metis
qed

lemma prop40ltr :
  assumes "s \<in> formulasemantics (mu (and' g (or (f) (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e"
  and "\<not>dependvari f M 0"
  and "\<not>dependvari g M 0"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "(\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) 
        \<and> (set (map action p) \<subseteq>  A) 
        \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (simp)
proof-
  have "mono (transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)" using assms(2) assms(3) assms(5) monotonicityformula40 by metis
  hence "s \<in> ((transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)^^(card (UNIV :: 's set))){}" using assms(1) assms(4) transformer_eq_mu by auto 
  thus "\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> formulasemantics (shiftdown f 0) M e
        \<and> action ` set p \<subseteq> A
        \<and> s \<in> formulasemantics (shiftdown g 0) M e
        \<and> target ` set p \<subseteq> formulasemantics (shiftdown g 0) M e" using prop40ltrinbetween assms(2) assms(3) assms(5) by metis
qed

(*simplifies independence to not occurs*)
lemma prop40 :
  assumes "\<not> dependvari f M 0"
  and "\<not> dependvari g M 0"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e) = 
    (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A) 
      \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (rule iffI)
  using assms prop40ltr apply metis
  using assms prop40rtl apply metis
  done

lemma invariantApath : 
  assumes "\<not> dependvari f M 0"
  and "S' \<subseteq> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'})"
  and "s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}"
  shows "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}"
proof-
  have "s \<in> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'})" using assms(2) assms(3) by auto
  hence "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<or>  (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S')" using assms(2) by auto
  moreover have "s \<notin> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" using assms(1) notdependshiftdown by metis
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action []) \<subseteq> A)" by auto
    thus False using assms(3) by blast
  qed
  ultimately have "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  from this obtain act s' where assum1 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "\<exists>p s''. s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A"
    from this obtain p s'' where "s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A" by auto
    hence "validfinpath M s ((s, act, s')#p) s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action ((s, act, s')#p)) \<subseteq> A)" using assum1 by simp
    thus False using assms(3) by blast
  qed
  thus ?thesis using assum1 by auto
qed

lemma theorem21generalizedltr : 
  assumes "\<not> dependvari f M 0"
  and "(s \<in> formulasemantics (nu (or f (Diamond (acts A) (var 0)))) M e)"
  and "finite A"
  shows "((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
    (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
proof-
  have "\<exists>S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(2) assms(3) by (simp del: Diamond.simps)
  from this obtain S' where assum1 : "S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" by auto
  have "(\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<Longrightarrow>  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))"
    apply (rule successorlemma)
  proof-
    assume assum2 : "\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A"
    let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}" 
    have "(\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))"
      apply (rule allI)
    proof
      fix s
      assume assum3 : "s \<in> ?S'"
      have "\<not> dependvari f M 0 \<Longrightarrow> S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<Longrightarrow> s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A} \<Longrightarrow> \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A}" using invariantApath by (simp)
      hence "\<exists>s'' act. act \<in> A \<and> (s, act, s'') \<in> (transition M) \<and> s'' \<in> ?S'" using assum1 assum3 assms(1) by simp
      thus "\<exists>t. source t = s \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S'" by auto
    qed
    moreover have "s \<in> ?S'" using assum1 assum2 by auto
    ultimately show "s \<in> ?S' \<and> (\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> action t \<in> A \<and> t \<in> transition M \<and> target t \<in> ?S')))" by simp
  qed
  thus ?thesis by auto
qed

lemma theorem21generalizedrtl : 
  assumes "\<not> dependvari f M 0"
  and "finite A"
  and "((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
     (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))" 
  shows "(s \<in> formulasemantics (nu (or f (Diamond (acts A) (var 0)))) M e)"
  apply (simp add: assms(2) del: Diamond.simps)
  apply (subst notdependshiftdown)
  apply (simp add: assms(1))
  apply (rule exI)
proof
  let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
              (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))}"
  show "s \<in> ?S'" using assms(3) by simp
  show "?S' \<subseteq> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}"
  proof
    fix s
    assume "s \<in> ?S'"
    moreover {  
      assume "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A"
      from this obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A" by auto
      have "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A \<Longrightarrow> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A))"
        apply (induct p arbitrary : s)
        apply (simp_all add: validfinpath.cases)
      proof-
        fix t p
        (*assum2 only needed for base case*)
        assume assum3 : "t \<in> transition M \<and> validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A"
        hence "(source t, action t, target t) \<in> transition M \<and> (validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A)" using splittransition by metis
        thus "source t \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (source t, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A))" by blast
      qed
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by auto
    }
    moreover {
      assume "\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)"
      from this obtain p where assum1 : "validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)" by auto
      hence "s = source (p 0) \<and> (p 0) \<in> transition M \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by (simp add: validinfpath_def)
      hence "(s, action (p 0), target (p 0)) \<in> transition M  \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by simp
      hence "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and>  (\<exists>p. validinfpath M s' p \<and> (\<forall>n. action (p n) \<in> A))" by blast
      hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by blast
   }
   ultimately show "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" by auto
 qed
qed

lemma theorem21generalized :  
  assumes "\<not> dependvari f M 0"
  and "finite A"
  shows "(s \<in> \<lbrakk>nu (or f (Diamond (acts A) (var 0)))\<rbrakk> M e) =
  ((\<exists>p s'. validfinpath M s p s' \<and> (set (map action p) \<subseteq> A) \<and> s' \<in> (formulasemantics (shiftdown f 0) M e)) \<or> 
  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
  apply (rule iffI)
  using assms theorem21generalizedltr apply metis
  using assms theorem21generalizedrtl apply metis
  done

lemma Boxcomplement_locked : "finite (-B) \<Longrightarrow> (s \<in> \<lbrakk>Box (acts (-B)) ff\<rbrakk> M e = locked M B s)"
  by (simp add: locked_def enabledactions_def del: Box.simps; auto)

lemma Diamond_enabled : "finite (\<alpha>\<^sub>e) \<Longrightarrow> (s \<in> \<lbrakk>Diamond (acts (\<alpha>\<^sub>e)) tt\<rbrakk> M e = enabled M s \<alpha>\<^sub>e)"
  by (simp add: enabled_def enabledactions_def del: Diamond.simps; auto)

lemma finitesubsetUNIV [simp] : "finite (UNIV :: 'a set) \<Longrightarrow> finite (A :: 'a set)"
  using finite_subset subset_UNIV by blast

lemma validfinpathmatchacts [simp] : "(validfinpath M s p s' \<and> match (acts A) p) = (\<exists>a \<in> A. (s, a, s') \<in> transition M \<and> p = [(s, a, s')])"
  by (simp add: match_def; auto)

lemma shiftupnotoccurs [simp] : "\<not>(occursvari (shiftup f i) i)"
  by (induct f arbitrary : i; simp)

lemma shiftuplemma [simp] : "\<lbrakk>shiftup f 0\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M e"
proof-
  have "(formulasemantics (shiftdown (shiftup f 0) 0) M (shiftdownenv (newenvironment e S') 0)) = (formulasemantics (shiftup f 0) M (newenvironment e S'))" using shiftupnotoccurs shiftdownlemma by metis
  thus "(formulasemantics (shiftup f 0) M (newenvironment e S')) = (formulasemantics f M e)" using shiftupanddown shiftdownnewenvzero_eq_newenv by metis
qed

lemma Diamondactsempty [simp] : "\<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>Diamond (acts A) f\<rbrakk> M e = {}"
proof-
  assume assum1: "\<lbrakk>f\<rbrakk> M e = {}"
  have "\<forall>listA. \<lbrakk>Diamondlist (listA) f\<rbrakk> M e = {}"
    apply (rule allI)
    apply (induct_tac listA; simp add: assum1)
    done
  thus "\<lbrakk>Diamond (acts A) f\<rbrakk> M e = {}" by auto
qed

lemma Diamondempty [simp] : "\<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>Diamond R f\<rbrakk> M e = {}"
  apply (induct R arbitrary : f e)
  prefer 2
  apply (rule Diamondactsempty)
  apply (simp_all)
  apply (auto)
  done

lemma inductionstepmatch :
  assumes "\<And>f s e. (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e) \<Longrightarrow> (s \<in> formulasemantics (Diamond (repeat R) f) M e)"
  apply (simp)
  apply (rule allI)
proof
  fix S'
  assume "\<exists>p s'. validfinpath M s p s' \<and> (\<exists>n. matchntimes n R p) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e"
  from this obtain p s' n where assum1 : " s' \<in> \<lbrakk>f\<rbrakk> M e \<and> matchntimes n R p \<and> validfinpath M s p s'" by auto
  assume assum2 : "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S') \<subseteq> S' \<and> \<lbrakk>f\<rbrakk> M e \<subseteq> S'"
  have "(s' \<in> \<lbrakk>f\<rbrakk> M e \<and> matchntimes n R p \<and> validfinpath M s p s') \<Longrightarrow> s \<in> S'"
    apply (induct n arbitrary: s p; simp)
    using assum1 assum2 emptypath apply blast
  proof-
    fix n s p
    assume assum3 : "(\<And>s p. matchntimes n R p \<and> validfinpath M s p s' \<Longrightarrow> s \<in> S')"
    assume "s' \<in> \<lbrakk>f\<rbrakk> M e \<and> (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'') \<and> validfinpath M s p s'"
    hence "\<exists>p' p'' s''. s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s p' s'' \<and> validfinpath M s'' p'' s'" by auto
    from this obtain p' p'' s'' where assum4 : "s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s p' s'' \<and> validfinpath M s'' p'' s'" by blast
    hence "s'' \<in> S'" using assum3 by auto
    hence "s'' \<in> \<lbrakk>var 0\<rbrakk> M (newenvironment e S')" by simp
    hence "(validfinpath M s p' s'' \<and> match R p' \<and> s'' \<in> \<lbrakk>var 0\<rbrakk> M (newenvironment e S'))" using assum4 by auto
    hence "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S')" using assms by auto
    thus "s \<in> S'" using assum2 by auto
  qed
  thus "s \<in> S'" using assum1 by auto
qed

lemma Diamondmatch :
  "finitereg R \<Longrightarrow> s \<in> \<lbrakk>Diamond R f\<rbrakk> M e = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)"
  apply (induct R arbitrary : f s e)
  apply simp
  apply (subst Diamond_eq_exist; simp; force)
  prefer 2
  apply auto[1]
  prefer 2
  unfolding finitereg.simps
proof
  fix R Q f s e
  assume "(\<And>f s e. finitereg R \<Longrightarrow> (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  hence assum1 : "finitereg R \<Longrightarrow> (s \<in> \<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>Diamond Q f\<rbrakk> M e)" by auto
  assume "(\<And>f s e. finitereg Q \<Longrightarrow> (s \<in> \<lbrakk>Diamond Q f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match Q p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  hence assum2 : "finitereg R \<Longrightarrow> finitereg Q \<Longrightarrow> (s \<in> \<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e) = (\<exists>p p' s''. (\<exists>s'. validfinpath M s p s' \<and> validfinpath M s' p' s'') \<and> match R p \<and> match Q p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" using assum1 by blast
  assume "finitereg R \<and> finitereg Q"
  thus "(s \<in> \<lbrakk>Diamond (after R Q) f\<rbrakk> M e) = (\<exists>p s''. validfinpath M s p s'' \<and> match (after R Q) p \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" using assum2 by auto
next
  fix R f s e
  show "(\<And>f s e. finitereg R \<Longrightarrow> (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)) \<Longrightarrow> finitereg R \<Longrightarrow>  \<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e \<Longrightarrow> s \<in> \<lbrakk>Diamond (repeat R) f\<rbrakk> M e" by (rule inductionstepmatch)
next
(*this can be done without matchntimes

assume assum1: "s \<in> \<lbrakk>f\<rbrakk> M e"
    have "match (repeat R) []" 
      apply (simp add: match_def)
      apply (subgoal_tac "[] \<in> regformtolanguage R ^^ 0")
      apply blast
      apply simp
      done
    hence "validfinpath M s [] s \<and> match (repeat R) [] \<and> s \<in> \<lbrakk>f\<rbrakk> M e" using assum1 by auto
    then show "s \<in> ?S'" by blast
*)
  fix R f s e
  assume assum1 : "(\<And>f s e. finitereg R \<Longrightarrow> (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  assume assum2 : "finitereg R"
  assume assum3 : "s \<in> \<lbrakk>Diamond (repeat R) f\<rbrakk> M e"
  let ?S' = "{s. \<exists>p s' n. validfinpath M s p s' \<and> matchntimes n R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  have "\<lbrakk>f\<rbrakk> M e \<subseteq> ?S'"
  proof (rule subsetI)
    fix s
    assume "s \<in> \<lbrakk>f\<rbrakk> M e"
    hence "validfinpath M s [] s \<and> matchntimes 0 R [] \<and> s \<in> \<lbrakk>f\<rbrakk> M e" by auto
    then show "s \<in> ?S'" by blast
  qed
  moreover have "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S') \<subseteq> ?S'"
  proof
    fix s 
    assume "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S')"
    hence "\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> ?S'" using assum1 assum2 by auto
    from this obtain p s' p' s'' n where assum3 : "validfinpath M s p s' \<and> match R p \<and> validfinpath M s' p' s'' \<and> matchntimes n R p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" by blast
    hence "validfinpath M s (p @ p') s''" using validfinpathsplit by metis
    moreover have "matchntimes (Suc n) R (p @ p') \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" using assum3 by auto
    ultimately show "s \<in> ?S'" by blast
  qed
  ultimately have "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S') \<union> \<lbrakk>f\<rbrakk> M e \<subseteq> ?S'" by auto
  thus "\<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e" using assum3 by auto
qed

lemma negformula [simp] : "(s \<in> \<lbrakk>neg f\<rbrakk> M e) = (s \<notin> \<lbrakk>f\<rbrakk> M e)"
  by simp

lemma notoccurs : "(\<not> occurs \<alpha>\<^sub>f (fin p)) = (action ` set p \<subseteq> -\<alpha>\<^sub>f)" by auto

lemma theorem21 :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (-B)"
  and "finitereg \<rho>"  (*introduce definition for finite regular formulas*)
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (-B)) ff)) (Diamond (acts (-\<alpha>\<^sub>f)) (var 0)))))\<rbrakk> M e 
    = (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p)"
  apply (subst negformula)
proof-
  have "\<forall>s. s \<in> \<lbrakk>Diamond \<rho> (nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (-B)) ff)) (Diamond (acts (-\<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e 
    = (\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p )"
    apply (subst Diamondmatch)
    apply (simp add: assms(2))
    apply (subst splitviolating)
  proof
    let ?A = "\<lambda>s'. s' \<in> \<lbrakk>nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (- B)) ff)) (Diamond (acts (- \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M e"
    let ?B = "\<lambda>s'.  (\<exists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s' p \<and> \<not> occurs \<alpha>\<^sub>f (inf p))"
    let ?C = "\<lambda>s'. (\<exists> p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p)"
    have res1 : "\<forall>s'. ?A s' = ?B s'"
      apply (subst theorem21generalized; simp add: notoccurs assms(1) assms(2) notoccursnotdepends Boxcomplement_locked Diamond_enabled del: Diamond.simps Box.simps Diamond_eq_exist Box_eq_forall occurs.simps(1))
      apply auto
      done
    moreover have res2: "\<forall>s'. ?C s' = ?B s'" by (subst splitcases; simp)
    have "\<forall>s'. ?A s' = ?C s'"
    proof
      fix s'
      show "?A s' = ?C s'"
        apply (subst res1)
        apply (subst res2)
        apply (auto)
        done
    qed
    thus "\<And>s. (\<exists>p s'. validfinpath M s p s' \<and> match \<rho> p \<and> s' \<in> \<lbrakk>nu (formula.or (formula.or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (- B)) ff)) (Diamond (acts (- \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M e) = (\<exists>p p' s'. match \<rho> p \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p')" by blast
  qed
  thus "(s \<notin> \<lbrakk>Diamond \<rho> (nu (formula.or (formula.or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (- B)) ff)) (Diamond (acts (- \<alpha>\<^sub>f)) (var 0))))\<rbrakk> M e) = (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p)" by blast
qed

lemma lemma50 : 
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> finite (\<alpha>\<^sub>_el a)"
  and "\<not>dependvari (\<phi>_off a) M 0"
  shows "s \<in> \<lbrakk>Diamond (repeat (acts (-\<alpha>\<^sub>f))) (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (acts ((\<alpha>\<^sub>_el a) -\<alpha>\<^sub>f)) (var 0)))\<rbrakk> M (newenvironment e S') 
    = (\<exists>p s'. validfinpath M s p s' \<and> (set (map action p) \<subseteq> -\<alpha>\<^sub>f \<and> 
        ((enabled M s' \<alpha>\<^sub>e) \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>s'' act. act \<in> ((\<alpha>\<^sub>_el a) - \<alpha>\<^sub>f) \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> S')) ))"
  apply (subst Diamondmatch)
  apply (simp add: assms)
  apply (subst matchrepeatact)
  apply (simp del: Diamond.simps add: assms enabled_def enabledactions_def)
  apply (subst notdependshiftdown; simp add: assms)
  apply fastforce
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
    moreover have "\<not> occurs \<alpha>\<^sub>f (fin (drop i p))" unfolding notoccurs using assum1 set_drop_subset by fastforce
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
    from this obtain a where assum2: "a \<in> A \<and> a \<in> (set (map action p))" by auto
    have "a \<in> (set (map action p)) \<longrightarrow> (\<exists>i < length p. a = action (p!i))" by (induction p; auto)
    from this obtain i where "i < length p \<and> a = action (p!i)" using assum2 by auto
    hence "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M \<and> action (p!i) \<in> A \<and> target (p!i) \<in> S'" using assum1 assum2 allstatesinS' by auto
    hence "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>a s''. (s', a, s'') \<in> transition M \<and> a \<in> A \<and> s'' \<in> S')" by blast
  }
  moreover {
    assume assum1: "validfinpath M s p s' \<and> occursstate S'' s (fin p)"
    hence "\<exists>s' \<in> S''. s' \<in> insert s (set (map target p))" by simp
    from this obtain s' where assum2: "s' \<in> S'' \<and> s' \<in> insert s (set (map target p))" by auto
    have "s' \<in> insert s (set (map target p)) \<longrightarrow> s' = s \<or> (\<exists>i < length p. s' = target (p!i))" by (induction p; auto)
    hence "s' = s \<or> (\<exists>i < length p. s' = target (p!i))" using assum2 by auto
    moreover have "s' = s \<Longrightarrow> validfinpath M s [] s \<and> s \<in> S' \<inter> S''"using assum2 assum1 allstatesinS' by auto
    moreover {
      assume "\<exists>i < length p. s' = target (p!i)" 
      from this obtain i where assum3 : "i < length p \<and> s'= target (p!i)" by auto
      hence "validfinpath M s (take i p) (source (p!i)) \<and> (source (p!i), action (p!i), target (p!i)) \<in> transition M" using assum1 by auto
      hence "validfinpath M s ((take i p) @ [(source (p!i), action (p!i), target (p!i))]) (target (p!i)) \<and> (target (p!i)) \<in> S''" using assum2 assum3 by (metis validfinpathsplit splittransition validfinpath.simps)
      moreover have "(target (p!i)) \<in> S'" using assum1 assum3 allstatesinS' by auto
      ultimately have "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" by auto
    }
    ultimately have "\<exists>p' s'. validfinpath M s p' s' \<and> s' \<in> S' \<inter> S''" by blast
  }
  ultimately show ?thesis using assms by blast
qed


(*function that maps to nth piece of path and function that then maps to nth transition*)


(*does lemma50 instead need to say general something on path is in shiftdown phi off a or alpha el a - alpha f*)
(*show that if validinfpath \<and> P s (inf p) then all states in p are in ?S' for rtl*)
(*why? because if not in ?S' then there does not exist a path , this is coinduction and maybe not possible*)


lemma hsifsb : "f ` set (l1 @ l2) = (f ` set l1) \<union> (f ` set l2)"
  by (simp add: image_Un)

lemma addpathsnotoccurs: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<Longrightarrow> validfinpath M s (p @ p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p @ p'))"
proof
  assume assum1 : "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p')"
  thus "validfinpath M s (p @ p') s''" using validfinpathsplit by meson
  have "action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> action ` set p' \<subseteq> - \<alpha>\<^sub>f" using assum1 by auto
  hence "(action ` set p \<union> action ` set p') \<subseteq> - \<alpha>\<^sub>f" by auto
  hence "action ` set (p@p') \<subseteq> - \<alpha>\<^sub>f" using image_Un by auto
  thus "\<not>occurs \<alpha>\<^sub>f (fin (p @ p'))" by auto
qed          

lemma notemptypath : "s \<notin> S' \<and> (occursstate S' s (fin p) \<or> occurs A (fin p)) \<longrightarrow> p \<noteq> []"
  by (induct p; simp)

(*lemma todo :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>a. finite (\<alpha>_el a)) \<and> finite (-B)"
  and "\<forall>a. \<not>(occursvari (\<phi>_off a) 0)"
  and "\<forall>a. \<not>(occursvari (\<phi>_on a) 0)"
  and invarfin: "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) = (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>i. action (p j) \<in> \<alpha>_el a \<or> target (p j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) ))))"
  and locking: "\<forall>s. (locked M B s = (\<forall> act \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e))"
  and exclusive: "\<forall>s. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e \<longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e " 
  and persistent: "\<forall>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s p  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"  
  and finite: "\<forall>s p s'. validfinpath M s p s' \<longrightarrow> ((\<exists>finextension s''. validfinpath M s (p @ finextension) s'' \<and> locked M B s'') \<or> (\<exists>infextension. validinfpath M s (conc p infextension) \<and> P s (inf (conc p infextension))))"
  shows "\<lbrakk>nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (repeat (acts (-\<alpha>\<^sub>f))) (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0))))))\<rbrakk> M e
    = {s. ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))}"
  apply (simp add: assms del: Diamond.simps occurs.simps locking)
  apply (subst lemma50; simp add: assms del: occurs.simps locking)
  apply (subst shiftdowncoro; simp add: assms del: occurs.simps locking)
  apply (rule subset_antisym)
  apply (rule Union_least)
  apply (rule subsetI)
  apply (rule CollectI)
  prefer 2
  apply (rule Union_upper)
  apply (rule CollectI)
  apply (rule INT_greatest)*)

(*lemma firstpathrecursiveconcpaths : "succ s \<noteq> [] \<Longrightarrow> recursiveconcpaths succ s a = conc (succ s) (recursiveconcpaths succ (target ((succ s) ! (length (succ s) - Suc 0))) a)"
  by (rule; simp)*)

(*unique j?, probably not due repitition*)
(*can possibly be easier using concipaths?*)
(*s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (target ((succ s) ! (length (succ s) - Suc 0))) \<in> S') \<and> i \<ge> Suc n \<Longrightarrow>*)
lemma existssplitpath : 
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate (succ s) \<in> S')" 
  shows "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix i (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)"
  apply (induct i)
proof-
  have "succ s \<noteq> [] \<Longrightarrow> recursiveconcpaths succ s a = conc (succ s) (recursiveconcpaths succ (laststate (succ s)) a)" by (rule; simp)
  hence "0 < length (succ s) \<and> s \<in> S' \<and> suffix 0 (recursiveconcpaths succ s a) = conc (drop 0 (succ s)) (recursiveconcpaths succ (laststate (succ s)) a)" using assms by auto
  thus "\<exists>j s'. j < length (succ s') \<and>  s' \<in> S' \<and> suffix 0 (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" by blast
next
  fix i
  assume "\<exists>j s'. j < length (succ s') \<and>  s' \<in> S' \<and> suffix i (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)"
  from this obtain j s' where IH: "j < length (succ s') \<and>  s' \<in> S' \<and> suffix i (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" by auto
  have "suffix (Suc i) (recursiveconcpaths succ s a) = suffix (Suc 0) (suffix i (recursiveconcpaths succ s a))" by auto
  moreover have "... = (conc (drop (Suc j) (succ s')) (recursiveconcpaths succ (laststate (succ s')) a))" using IH by auto
  ultimately have IH: "j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s a) = (conc (drop (Suc j) (succ s')) (recursiveconcpaths succ (laststate (succ s')) a))" using IH by simp
  {
    assume assum2: "Suc j < length (succ s')"
    hence "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" using IH by auto
  }
  moreover {
    assume assum2: "Suc j \<ge> length (succ s')"
    let ?s = "laststate (succ s')"
    have "suffix (Suc i) (recursiveconcpaths succ s a) = recursiveconcpaths succ ?s a" using assum2 IH by auto
    moreover have "succ ?s \<noteq> [] \<Longrightarrow> recursiveconcpaths succ ?s a = conc (succ ?s) (recursiveconcpaths succ (laststate (succ ?s)) a)" by (rule; simp)
    moreover have "succ ?s \<noteq> []" using assms IH by auto
    ultimately have "0 < length (succ ?s) \<and> suffix (Suc i) (recursiveconcpaths succ s a) = conc (succ ?s) (recursiveconcpaths succ (laststate (succ ?s)) a)" by simp
    moreover have "drop 0 (succ ?s) = succ ?s" by auto
    ultimately have "0 < length (succ ?s) \<and> ?s \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s a) = conc (drop 0 (succ ?s)) (recursiveconcpaths succ (laststate (succ ?s)) a)" using assms IH by metis
    hence "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" by blast
  }
  ultimately show "\<exists>j s'. j < length (succ s') \<and> s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s a) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" using not_le_imp_less by auto
qed

lemma succe : 
  assumes "s \<in> S'"
  (*and "s \<in> S' \<Longrightarrow> " not exists path ending in block state*)
  and persistent: "\<forall>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
 
  and "\<forall>s' \<in> S'. \<exists>p s''. p \<noteq> [] \<and> validfinpath M s' p s'' \<and> s'' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))"
  shows "\<exists>p'. validinfpath M s p' \<and> \<not>occurs \<alpha>\<^sub>f (inf p') \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' i)) (inf (suffix i p'))))))"
proof-
  fix a :: 'b
  have "\<forall>s' \<in> S'. \<exists>p. p \<noteq> [] \<and> validfinpath M s' p (laststate p) \<and> laststate p \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" 
  proof
    fix s'
    assume "s' \<in> S'"
    from this obtain p s'' where "p \<noteq> [] \<and> validfinpath M s' p s'' \<and> s'' \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using assms(3) by auto
    thus "\<exists>p. p \<noteq> [] \<and> validfinpath M s' p (laststate p) \<and> laststate p \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using validfinpathlaststate by metis
  qed
  from this obtain succ where assum1: "\<forall>s' \<in> S'. succ s' \<noteq> [] \<and> validfinpath M s' (succ s') (laststate (succ s')) \<and> laststate (succ s') \<in> S' \<and> \<not>occurs \<alpha>\<^sub>f (fin (succ s')) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin (succ s')) \<or> occurs (\<alpha>_el a) (fin (succ s')))" by metis
  let ?p = "recursiveconcpaths succ s a"
  have validinfpath : "validinfpath M s ?p" using validinfpathconc assum1 assms(1) by metis
  have "\<forall>n. action (recursiveconcpaths succ s a n) \<notin> \<alpha>\<^sub>f" 
    apply (subst validpredconc [where ?P="\<lambda>s. \<lambda>t. action (t) \<notin> \<alpha>\<^sub>f" and ?Q="\<lambda>s. \<lambda>p. \<not>occurs \<alpha>\<^sub>f (fin p)"])
    using assms(1) assum1 apply auto
    done
  hence alphaffree : "\<not> occurs \<alpha>\<^sub>f (inf ?p)" by simp
  have "(((\<forall>i. \<forall>a \<in> -B. (source (?p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))))))"
    apply (rule allI)
  proof
    fix i act
    assume actinBcomp : "act \<in> -B"
    show "source (?p i) \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e \<longrightarrow> occurs (\<alpha>_el act) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))"
    proof
      assume "source (?p i) \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e"
      obtain j s' where "j < length (succ s') \<and> s' \<in> S' \<and> suffix i ?p = conc (drop j (succ s')) (recursiveconcpaths succ (laststate (succ s')) a)" using existssplitpath assum1 assms(1) by metis
      moreover from this have "recursiveconcpaths succ (laststate (succ s')) a =  conc (succ (laststate (succ s'))) (recursiveconcpaths succ (laststate (succ (laststate (succ s')))) a)" using assum1 by auto
      ultimately have assum2: "j < length (succ s') \<and> s' \<in> S' \<and> suffix i ?p = conc (drop j (succ s')) (conc (succ (laststate (succ s'))) (recursiveconcpaths succ (laststate (succ (laststate (succ s')))) a))" by auto 
      have "occurs (\<alpha>_el act) (fin (drop j (succ s'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s'))) \<or> occurs (\<alpha>_el act) (fin (succ (laststate (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s'))))"
      proof-
        have "validinfpath M s (conc (prefix i ?p) (suffix i ?p))" using validinfpath by auto
        hence "\<exists>s'. validfinpath M s (prefix i ?p) s' \<and> validinfpath M s' (suffix i ?p)" using validinfpathsplit by metis
        hence "validinfpath M (source (?p i)) (suffix i ?p)" using validinfpath validinfsubpathright by metis
        moreover have "(drop j (succ s')) \<noteq> []" using assum2 by auto
        ultimately have "validfinpath M (source (?p i)) (drop j (succ s')) (laststate (succ s'))" using laststatedrop validinfpathsplitlaststate assum2 by metis
        { 
          moreover assume "\<not>occurs (\<alpha>_el act) (fin (drop j (succ s'))) \<and> \<not>occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s')))"
          ultimately have "laststate (succ s') \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e" using persistent actinBcomp by metis
          hence "occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s')))) \<or> occurs (\<alpha>_el act) (fin (succ (laststate (succ s'))))" using assum1 assum2 actinBcomp by metis
        }
        thus ?thesis by blast
      qed
      moreover have "occurs (\<alpha>_el act) (fin (drop j (succ s'))) \<or> occurs (\<alpha>_el act) (fin (succ (laststate (succ s')))) \<Longrightarrow> occurs (\<alpha>_el act) (fin (drop j (succ s') @ succ (laststate (succ s'))))" by auto
      moreover have "occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s'))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (laststate (succ s')) (fin (succ (laststate (succ s')))) \<Longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s') @ succ (laststate (succ s'))))" using occursstatefin occursstatefinright assum2
        by (metis drop_eq_Nil2 laststatedrop linorder_not_le) (*this should be better*)
      ultimately have "occurs (\<alpha>_el act) (fin (drop j (succ s') @ succ (laststate (succ s')))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (fin (drop j (succ s') @ succ (laststate (succ s'))))" by metis
      moreover have "suffix i ?p = conc (drop j (succ s') @ succ (laststate (succ s'))) (recursiveconcpaths succ (laststate (succ (laststate (succ s')))) a)" using assum2 by auto
      ultimately show "occurs (\<alpha>_el act) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))" using occursstateinf occursinf by metis
    qed
  qed
  hence "validinfpath M s ?p \<and> \<not>occurs \<alpha>\<^sub>f (inf ?p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (?p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i ?p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (?p i)) (inf (suffix i ?p))))))" using validinfpath alphaffree by auto
  thus ?thesis by blast
qed

(*lemma occursfinsubpath : "occurs A (fin p) \<longrightarrow> (\<exists>i < length p. action (p!i) \<in> A)"
  by (induct p; auto)*)

lemma notoccursfinpath [simp] : "action ` set p \<subseteq> -A = (\<not> occurs A (fin p))"
  by auto

lemma infpathoccursoroccursstate : 
  assumes "validinfpath M s p \<and> (occurs A (inf p) \<or> occursstate S' s (inf p))"
  shows "\<exists>i. source (p i) \<in> S' \<or> action (p i) \<in> A" 
  using validinfpathoccursstate assms occurs.simps(2) by metis   

lemma todo :
  assumes "finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>a. finite (\<alpha>_el a)) \<and> finite (-B)"
  and "\<forall>a. \<not>dependvari (\<phi>_off a) M 0"
  and "\<forall>a. \<not>dependvari (\<phi>_on a) M 0"
  and invarfin: "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and locking: "\<forall>s. (locked M B s = (\<forall> act \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e))"
  and exclusive: "\<forall>s. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e " 
  and persistent: "\<forall>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and finite: "\<forall>s p s'. validfinpath M s p s' \<longrightarrow> ((\<exists>finextension s''. validfinpath M s (p @ finextension) s'' \<and> locked M B s'') \<or> (\<exists>infextension. validinfpath M s (conc p infextension) \<and> P s (inf (conc p infextension))))"
  shows "s \<in> \<lbrakk>nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (repeat (acts (-\<alpha>\<^sub>f))) (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0))))))\<rbrakk> M e
    = ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
  apply (simp add: assms del: Diamond.simps occurs.simps locking)
  apply (subst lemma50; simp add: assms del: occurs.simps locking)
  apply (subst notdependshiftdown)
  apply (simp add: assms del: occurs.simps locking)
proof
  assume "\<exists>S'. S' \<subseteq> (\<Inter>act\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) \<or> (\<exists>s'' a. a \<in> \<alpha>_el act \<and> a \<notin> \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'"
  from this obtain S' where assum1: "S' \<subseteq> (\<Inter>act\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) \<or> (\<exists>s'' a. a \<in> \<alpha>_el act \<and> a \<notin> \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> S')))}) \<and> s \<in> S'" by auto
  let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)}"
  have inS': "\<forall>p s s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> s \<in> ?S' \<and> s' \<in> S' \<longrightarrow> s' \<in> ?S'"
    apply (rule allI)+
  proof
    fix p s s'
    assume assum1: "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> s \<in> ?S' \<and> s' \<in> S'"
    have "\<nexists>p s''. validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)"
    proof
      assume "\<exists>p' s''. validfinpath M s' p' s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)"
      from this obtain p' s'' where "validfinpath M s' p' s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" by auto
      hence "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s' p' s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" using assum1 by auto
      hence "validfinpath M s (p@p') s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin (p@p')) \<and> (locked M B s'' \<or> enabled M s'' \<alpha>\<^sub>e)" using addpathsnotoccurs by metis
      hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)" by blast
      hence "s \<notin> ?S'" by auto
      thus False using assum1 by blast
    qed
    thus "s' \<in> ?S'" using assum1 by blast
  qed
  have succfinpaths: "\<forall>s' \<in> ?S'. \<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))"
  proof
    fix s'
    assume assum2: "s' \<in> ?S'"
    let ?L = "{a \<in> -B. s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e}"
    have "\<forall>n. \<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow> (\<exists>p s''. validfinpath M s' p s'' \<and> (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
    proof
      fix n
      show "\<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow>  (\<exists>p s''. validfinpath M s' p s'' \<and> (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
        apply (induct n; rule allI; rule impI)
      proof
        let ?p = "[]"
        fix L :: "'a set"
        assume assum3 : "card L = 0 \<and> L \<subseteq> ?L"
        hence "L \<subseteq> (-B) \<and> finite (-B)" using assms(1) by auto
        hence "finite L" using assms(1) finite_subset by auto
        hence "L = {}" using assum3 by auto
        hence "validfinpath M s' ?p s' \<and> (L \<noteq> {} \<longrightarrow> ?p \<noteq> []) \<and> s' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin ?p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin ?p) \<or> occurs (\<alpha>_el a) (fin ?p))" using assum2 by auto
        thus "\<exists>s''. validfinpath M s' ?p s'' \<and> (L \<noteq> {} \<longrightarrow> ?p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin ?p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin ?p) \<or> occurs (\<alpha>_el a) (fin ?p))" by auto
      next
        fix n 
        fix L :: "'a set"
        assume IH : "\<forall>L. card L = n \<and> L \<subseteq> ?L \<longrightarrow> (\<exists>p s''. validfinpath M s' p s'' \<and> (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p)))"
        assume assum3: "card L = Suc n \<and> L \<subseteq> ?L"
        hence "card L = Suc n" by auto
        hence "\<exists>a L'. L = insert a L' \<and> a \<notin> L' \<and> card L' = n \<and> (n = 0 \<longrightarrow> L' = {})" by (rule card_eq_SucD)
        from this obtain a L' where assum4: "L = insert a L' \<and> a \<notin> L' \<and> card L' = n" by auto
        hence "card L' = n \<and> L' \<subseteq> ?L" using assum3 by auto
        hence "\<exists>p s''. validfinpath M s' p s'' \<and> (L' \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and>  \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L' \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using IH by auto   
        from this obtain p s'' where assum5: "validfinpath M s' p s'' \<and> (L' \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and>  \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L' \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto      
        have "(occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p)) \<or> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<and> \<not>occurs (\<alpha>_el a) (fin p))" by auto
        moreover {
          assume assum6: "occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p)"
          have "a \<in> ?L" using assum4 assum3 by auto
          hence "p \<noteq> []" using exclusive occursstateempty occursempty assum6 by auto
          hence "validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using assum4 assum5 assum6 by auto
          hence "\<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> []  \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto
        }
        moreover {
          assume assum6 : "\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<and> \<not>occurs (\<alpha>_el a) (fin p)"
          have ainBcomp : "a \<in> -B" using assum3 assum4 by auto
          have "s'' \<in> (\<Inter>act\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off act) 0\<rbrakk> M e) \<or> (\<exists>s'' a. a \<in> \<alpha>_el act \<and> a \<notin> \<alpha>\<^sub>f \<and> (s', a, s'') \<in> transition M \<and> s'' \<in> S')))})" using assum1 assum5 by auto
          hence "s'' \<in> {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>t3 t2. t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s', t2, t3) \<in> transition M \<and> t3 \<in> S')))}" using ainBcomp by blast
          hence "\<exists>p s'. validfinpath M s'' p s' \<and> action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s' \<alpha>\<^sub>e \<or> (s' \<in> S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>t3 t2. t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s', t2, t3) \<in> transition M \<and> t3 \<in> S'))" using ainBcomp assum5 assum6 persistent by auto
          from this obtain p' s''' where pathextension: "validfinpath M s'' p' s''' \<and> action ` set p' \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s''' \<alpha>\<^sub>e \<or> (s''' \<in> S' \<and> s''' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>t3 t2. t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s''', t2, t3) \<in> transition M \<and> t3 \<in> S'))" by auto  
          hence "validfinpath M s' p s'' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s'' p' s''' \<and> \<not> occurs \<alpha>\<^sub>f (fin p')" using assum5 by auto
          hence validaddpath: "validfinpath M s' (p@p') s''' \<and> \<not> occurs \<alpha>\<^sub>f (fin (p@p'))" using addpathsnotoccurs by metis
          have "enabled M s''' \<alpha>\<^sub>e \<or> (s''' \<in> S' \<and> s''' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) \<or> (\<exists>t3 t2. t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s''', t2, t3) \<in> transition M \<and> t3 \<in> S')" using pathextension by simp
          moreover  { 
            assume "enabled M s''' \<alpha>\<^sub>e"
            hence "s' \<notin> ?S'" using validaddpath by blast
            hence False using assum2 by auto
          }
          moreover {
            assume occursstate: "s''' \<in> S' \<and> s''' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e"
            hence "validfinpath M s' (p@p') s''' \<and> (\<exists>s''\<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e. s'' \<in> insert s''' (set (map source (p@p'))))" using validaddpath by blast
            hence "occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin (p@p'))" using validpathoccursstate by metis
            moreover from this have "p' \<noteq> []" using assum6 by force
            moreover have "(\<forall>a. a \<in> L' \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin (p@p')) \<or> occurs (\<alpha>_el a) (fin (p@p')))" using assum5 occursextension occursstatefin by metis
            ultimately have "p@p' \<noteq> [] \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin (p@p')) \<or> occurs (\<alpha>_el a) (fin (p@p')))" using assum4 by auto
            moreover have "s''' \<in> ?S'" using inS' validaddpath occursstate assum2 by blast
            ultimately have "\<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using validaddpath by blast
          }
          moreover {
            assume "\<exists>t3 t2. t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s''', t2, t3) \<in> transition M \<and> t3 \<in> S'"
            from this obtain t2 t3 where actinalphael : "t2 \<in> \<alpha>_el a \<and> t2 \<notin> \<alpha>\<^sub>f \<and> (s''', t2, t3) \<in> transition M \<and> t3 \<in> S'" by auto
            hence "validfinpath M s''' [(s''', t2, t3)] t3 \<and>  \<not> occurs \<alpha>\<^sub>f (fin ([(s''', t2, t3)]))" by auto
            hence validaddpath: "validfinpath M s' ((p@p')@[(s''', t2, t3)]) t3 \<and> \<not> occurs \<alpha>\<^sub>f (fin ((p@p')@[(s''', t2, t3)]))" using addpathsnotoccurs validaddpath by metis
            have "t2 \<in> (set (map action ((p@p')@[(s''', t2, t3)])))" by auto
            hence "occurs (\<alpha>_el a) (fin ((p@p')@[(s''', t2, t3)]))" using actinalphael by auto
            moreover have "(\<forall>a. a \<in> L' \<longrightarrow>  occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin ((p@p')@[(s''', t2, t3)])) \<or> occurs (\<alpha>_el a) (fin ((p@p')@[(s''', t2, t3)])))" using assum5 occursstatefin occursextension by metis
            ultimately have "\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin ((p@p')@[(s''', t2, t3)])) \<or> occurs (\<alpha>_el a) (fin ((p@p')@[(s''', t2, t3)]))" using assum4 by auto
            moreover have "t3 \<in> ?S'" using inS' validaddpath actinalphael assum2 by blast
            ultimately have "\<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" using validaddpath by blast  
          }
          ultimately have "\<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto
        } 
        ultimately show "\<exists>p s''. validfinpath M s' p s'' \<and> (L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
      qed
    qed
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> (?L \<noteq> {} \<longrightarrow> p \<noteq> []) \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> ?L \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by blast
    moreover have "?L \<noteq> {}"
    proof
      assume "{a \<in> - B. s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e} = {}"
      hence "validfinpath M s' [] s' \<and> locked M B s' \<and> \<not> occurs \<alpha>\<^sub>f (fin [])" using locking by auto
      thus False using assum2 by blast
    qed
    ultimately show "\<exists>p s''. validfinpath M s' p s'' \<and> p \<noteq> [] \<and> s'' \<in> ?S' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (\<forall>a. a \<in> -B \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s' (fin p) \<or> occurs (\<alpha>_el a) (fin p))" by auto
  qed
(*maybe not occurs should not always be simplified*)
(*moreover have L is never empty and therefore the paths is always longer than 1*)
  have "\<nexists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e) \<Longrightarrow> \<exists>p'. validinfpath M s p' \<and> \<not>occurs \<alpha>\<^sub>f (inf p') \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p' i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p')) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p' i)) (inf (suffix i p'))))))" 
      apply (subst succe [where ?S' = "?S'"])
      using assum1 apply simp
      using persistent apply simp
      using succfinpaths apply meson
      apply simp
      done
   thus "((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))" using invarinf by metis
next
  let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))}"
  assume "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))"
  hence "s \<in> ?S'" by simp
  moreover have "?S' \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S')))})"
    apply (rule)
    apply (rule)
    apply (rule)
  proof
    fix s a
    assume assum1: "s \<in> ?S'"
    assume assum2 : "a \<in> -B"
    assume assum3 : "s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
    (*have "s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> action ` set p \<subseteq> - \<alpha>\<^sub>f \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>\<^sub>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S')))"*)
(*this next one is simplified when we instead say that it occurs somewhere instead of in the last transition*)
    show "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S'))"
    proof-
      have "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)) \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p))" using assum1 by auto
      moreover {
        assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e)"
        hence "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)" by auto
        moreover {
          assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'"
          from this obtain p s' where assum4: "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s'" by auto
          moreover have "occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)"
            apply (rule ccontr)
            apply (subgoal_tac "s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e")
            using assms(6) assum2 assum4 apply blast
            using assms(8) assum2 assum4 apply blast
            done
          ultimately have "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s' \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p))" by auto
          moreover have "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (occurs (\<alpha>_el a) (fin p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)) \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p)  \<and> ((s' \<in> ?S' \<inter> (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)) \<or> (\<exists>act s''. (s', act, s'') \<in> transition M \<and> act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> s'' \<in> ?S')))"
            apply (induct p)
            using assum2 assum3 exclusive apply auto[1]
            apply (metis (no_types, lifting) Int_Collect Int_commute assum2 assum4 locking
                occursempty occursstateempty persistent validfinpath.simps(1)) (*should do*)
            done
(*is there a good way to split [] and other paths here*)
          ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> ((s' \<in> ?S' \<inter> (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)) \<or> (\<exists>act s''. (s', act, s'') \<in> transition M \<and> act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> s'' \<in> ?S'))" by simp
        }
        ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> ?S' \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> ?S'))" by blast
      }
      moreover {
        assume "\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)"
        from this obtain p where predP: "validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p))))))" using invarinf by auto
        moreover from this have "source (p 0) = s \<and> suffix 0 p = p" by (simp add: validinfpath_def)
        ultimately have validinfpath: "validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p) \<and> (occurs (\<alpha>_el a) (inf p) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (inf p))" using assum2 assum3 by metis
        from this obtain i where sourceoraction : "source (p i) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> action (p i) \<in> \<alpha>_el a" using infpathoccursoroccursstate by metis
        have "\<And>j. source (p j) \<in> ?S'"
        proof-
          fix j
          have "validinfpath M (source (p j)) (suffix j p) \<and> \<not> occurs \<alpha>\<^sub>f (inf (suffix j p)) \<and> P (source (p j)) (inf (suffix j p))"
          proof-
            have "(\<forall>a \<in> -B. ((\<forall>k. (source ((suffix j p) k)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix k (suffix j p))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source ((suffix j p) k)) (inf (suffix k (suffix j p)))))))" using predP by simp
            moreover have "validinfpath M (source (p j)) (suffix j p) \<and>  \<not> occurs \<alpha>\<^sub>f (inf (suffix j p))" using predP by auto
            ultimately show ?thesis using invarinf by metis
          qed
          thus "source (p j) \<in> ?S'" by auto
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
  ultimately show "\<exists>x. x \<subseteq> (\<Inter>a\<in>- B. {s. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (enabled M s' \<alpha>\<^sub>e \<or> s' \<in> x \<and> s' \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e \<or> (\<exists>s'' act. act \<in> \<alpha>_el a \<and> act \<notin> \<alpha>\<^sub>f \<and> (s', act, s'') \<in> transition M \<and> s'' \<in> x)))}) \<and> s \<in> x" by blast
qed

lemma predPsubpath :
  assumes  invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  shows "validinfpath M s p \<and> P s (inf p) \<Longrightarrow> validinfpath M (source (p i)) (suffix i p) \<and> P (source (p i)) (inf (suffix i p))"
proof-
  assume assum1 : "validinfpath M s p \<and> P s (inf p)"
  hence "\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))" using invarinf by auto
  hence "(\<forall>a \<in> -B. ((\<forall>j. (source ((suffix i p) j)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix j (suffix i p))) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source ((suffix i p) j)) (inf (suffix j (suffix i p)))))))" by simp
  moreover have "validinfpath M (source (p i)) (suffix i p)" using assum1 by auto
  ultimately show ?thesis using invarinf by metis  
qed

lemma theorem24 :
  assumes "finitereg \<rho> \<and> finite (-\<alpha>\<^sub>f) \<and> finite \<alpha>\<^sub>e \<and> (\<forall>a. finite (\<alpha>_el a)) \<and> finite (-B)"
  and "\<forall>a. \<not>dependvari (\<phi>_off a) M 0"
  and "\<forall>a. \<not>dependvari (\<phi>_on a) M 0"

  and invarfin: "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and invarinf: "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) =  (\<forall>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (occurs (\<alpha>_el a) (inf (suffix i p)) \<or> occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) (source (p i)) (inf (suffix i p)))))))"
  and locking: "\<forall>s. (locked M B s = (\<forall> act \<in> -B. s \<notin> \<lbrakk>shiftdown (\<phi>_on act) 0\<rbrakk> M e))"
  and exclusive: "\<forall>s. \<forall>a \<in> -B. s \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> s \<notin> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e " 
  and persistent: "\<forall>s p s' a. a \<in> -B \<and> validfinpath M s p s' \<and> (\<not>occursstate (\<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) s (fin p)  \<and> \<not>occurs (\<alpha>_el a) (fin p)) \<longrightarrow> s' \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
  and finite: "\<forall>s p s'. validfinpath M s p s' \<longrightarrow> ((\<exists>finextension s''. validfinpath M s (p @ finextension) s'' \<and> locked M B s'') \<or> (\<exists>infextension. validinfpath M s (conc p infextension) \<and> P s (inf (conc p infextension))))"
 
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (repeat (acts (-\<alpha>\<^sub>f))) (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0))))))))\<rbrakk> M e =
  (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p)"
proof-
  have res1: "\<forall>s. (s \<in> \<lbrakk>Diamond \<rho> (nu (And (-B) (\<lambda>a. or (neg (\<phi>_on a)) (Diamond (repeat (acts (-\<alpha>\<^sub>f))) (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (and' (\<phi>_off a) (var 0))) (Diamond (acts ((\<alpha>_el a) -\<alpha>\<^sub>f)) (var 0)))))))\<rbrakk> M e =
  (\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and>  progressing M s B p \<and> P s p))"
    apply (subst Diamondmatch)
    apply (simp add: assms(1))
    apply (subst splitviolating' [where ?\<phi>_on="\<phi>_on" and ?\<phi>_off="\<phi>_off" and ?\<alpha>_el="\<alpha>_el" and ?e="e"])
    using invarfin apply simp
    using invarinf apply simp
    using persistent apply simp
    apply (subst todo [where P="P"])
    apply (simp add: assms) apply (simp add: assms) apply (simp add: assms) 
    using invarfin apply simp
    using invarinf apply simp
    using locking apply simp
    using exclusive apply simp
    using persistent apply simp
    using finite apply simp
    apply (subst splitcases')
    using invarfin apply simp
    using finite apply simp
    apply fastforce
    done
  thus ?thesis by (subst negformula; blast)
qed
