theory Base
  imports Main HOL.Orderings Common
begin

type_synonym 'a relation = "'a \<Rightarrow> 'a \<Rightarrow> bool"

(*
  A preference profile is a tuple containing a preference relation for each voter 
*)
type_synonym 'a PP = "nat \<Rightarrow> 'a relation"

locale choice_setting =
  (* The nonempty finite universe of alternatives *)
  fixes U :: "'a set"
  assumes nonempty_universe: "U \<noteq> {}"
  assumes finite_universe: "finite U"

locale social_choice_setting = choice_setting +
  (* The amount of voters *)
  fixes n :: nat
  assumes n_pos: "n > 0"
begin

(* The finite set of voters, actually just a set {0, 1, ..., n} *)
abbreviation N where "N \<equiv> {i . i < n}"
lemma filled_N: "filled N" by (metis empty_def finite_Collect_less_nat mem_Collect_eq n_pos)
lemma filled_G: "G \<sqsubseteq> N \<Longrightarrow> filled G" by (metis filled_N sub_finite) 

end

abbreviation asymm :: "'a relation \<Rightarrow> 'a relation" where "asymm R \<equiv> \<lambda>x y. R x y \<and> \<not> R y x"

locale general_preference = choice_setting +
  (* x R y means that x is at least as good as y, possibly indifferent *)
  fixes R :: "'a relation" (infix "R" 50)
  (* R never relates elements that are not alternatives *)
  assumes R_domain: "(x \<notin> U \<or> y \<notin> U) \<Longrightarrow> \<not> x R y"
begin

(* The asymmetric part of R, i.e. x P y means that x is strictly better than y *)
definition P :: "'a relation" (infix "P" 50) where "(P) \<equiv> asymm (R)"

lemma P_subrelation_of_R: "x P y \<Longrightarrow> x R y" using P_def by simp

definition Max :: "'a set \<Rightarrow> 'a set" where "Max A = {x \<in> A . \<not>(\<exists>y \<in> A . y P x)}"

end

locale transitive_preference = general_preference +
  assumes transitive: "x R y \<Longrightarrow> y R z \<Longrightarrow> x R z"
begin

lemma P_trans: "x P y \<Longrightarrow> y P z \<Longrightarrow> x P z" unfolding P_def using transitive by blast
lemma P_trans2: "x P y \<Longrightarrow> z R x \<Longrightarrow> z P y" unfolding P_def using transitive by blast

lemma Max_nonempty: "A \<sqsubseteq> U \<Longrightarrow> Max A \<noteq> {}" proof -
  assume "A \<sqsubseteq> U"
  hence "finite A" using finite_universe rev_finite_subset by auto 
  thus "A \<sqsubseteq> U \<Longrightarrow> Max A \<noteq> {}" proof (induction rule: finite_psubset_induct)
    case (psubset A)
    then obtain a where a: "a \<in> A" by auto
    let ?B = "{b \<in> A. b P a}"
    show ?case proof (cases "?B = {}")
      case True
      thus ?thesis using P_def Max_def[of A] \<open>a \<in> A\<close> by auto
    next
      case False
      then obtain bmax where "bmax \<in> Max ?B" using psubset.prems P_def a psubset.IH[of ?B] by auto
      moreover
      hence "bmax P a" unfolding P_def Max_def by auto
      hence "y R bmax \<Longrightarrow> y P a" for y using P_trans2 by auto
      ultimately 
      show ?thesis unfolding P_def Max_def by auto
    qed
  qed
qed

end

locale reflexive_preference = general_preference +
  assumes reflexive: "x \<in> U \<Longrightarrow> x R x"

locale complete_preference = general_preference +
  assumes complete: "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x R y \<or> y R x"
begin

lemma Max_comp: "A \<sqsubseteq> U \<Longrightarrow> Max A = {x \<in> A . (\<forall>y \<in> A . x R y)}" unfolding Max_def using complete
  by (metis (mono_tags, lifting) P_def in_mono) 

end

(* We usually assume that individual preference relations are complete, reflexive, and transitive *)
locale preference_relation = transitive_preference + reflexive_preference + complete_preference

context choice_setting
begin
definition triv_pref where "triv_pref \<equiv> \<lambda>x y. x \<in> U \<and> y \<in> U"
interpretation triv_pref: preference_relation U triv_pref 
  unfolding triv_pref_def by unfold_locales auto

end

locale preference_profile = social_choice_setting +
  constrains U :: "'a set"
  fixes R\<^sub>N :: "'a PP"
  assumes R\<^sub>N: "i \<in> N \<Longrightarrow> preference_relation U (R\<^sub>N i)"
  assumes R\<^sub>N_domain: "i \<notin> N \<or> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R\<^sub>N i x y"
begin
abbreviation P\<^sub>N :: "'a PP" where "P\<^sub>N i x y \<equiv> i \<in> N \<and> general_preference.P (R\<^sub>N i) x y"

lemma refl: "i \<in> N \<Longrightarrow> a \<in> U \<Longrightarrow> R\<^sub>N i a a" proof -
  fix i a 
  assume "i \<in> N"
  hence "reflexive_preference U (R\<^sub>N i)" using R\<^sub>N by (auto simp add: preference_relation.axioms(2))
  moreover assume "a \<in> U"
  ultimately show "R\<^sub>N i a a" using reflexive_preference.reflexive[of U] by auto
qed

end

end