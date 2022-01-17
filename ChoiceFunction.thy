theory ChoiceFunction
  imports Main Common Base
begin

(* A choice function maps a set of presented alternatives to a set of chosen alternatives *)
type_synonym 'a CF = "'a set \<Rightarrow> 'a set"

abbreviation invalid_cf :: "'a CF" where "invalid_cf \<equiv> \<lambda>_. {}"
abbreviation trivial_cf :: "'a CF" where "trivial_cf \<equiv> id"

locale choice_function = choice_setting +
  constrains U :: "'a set"
  fixes S :: "'a CF"
  (* S has to choose some nonempty subset of the given alternatives A *)
  assumes S: "A \<sqsubseteq> U \<Longrightarrow> S A \<sqsubseteq> A"
  assumes S_domain: "(\<not> A \<sqsubseteq> U) = (S A = invalid_cf A)"
begin

lemma S_subset: "S A \<subseteq> A" using S S_domain by (cases "A \<sqsubseteq> U") auto

(* The base relation of S *)
definition R\<^sub>S (infixl "R\<^sub>S" 50) where "x R\<^sub>S y = (x \<in> S {x, y})"
interpretation base_complete: complete_preference U "(R\<^sub>S)" proof
  show "\<And>x y. x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> x R\<^sub>S y" unfolding R\<^sub>S_def using S_domain by auto next
  show "\<And>x y. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x R\<^sub>S y \<or> y R\<^sub>S x" unfolding R\<^sub>S_def by (smt (verit) Diff_eq_empty_iff Diff_insert_absorb S Un_Diff_cancel Un_upper1 insert_Diff insert_commute insert_is_Un insert_not_empty insert_subsetI subset_insert) 
qed
lemma base_complete: "complete_preference U (R\<^sub>S)" by (simp add: base_complete.complete_preference_axioms) 

lemma eq_base_max: "A \<sqsubseteq> U \<Longrightarrow> x \<in> A \<Longrightarrow> (\<forall>y \<in> A. x \<in> S {x, y}) = (x \<in> general_preference.Max (R\<^sub>S) A)" using base_complete.Max_comp R\<^sub>S_def by auto

lemma trivial_choice: "x \<in> U \<Longrightarrow> S {x} = {x}" using S[of "{x}"] by auto

end

(* Contraction *)
locale sat_\<alpha> = choice_function +
  assumes \<alpha>: "A \<sqsubseteq> U \<Longrightarrow> B \<sqsubseteq> U \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> S (A \<union> B) \<Longrightarrow> x \<in> S A \<and> x \<in> S B"

(* Expansion *)
locale sat_\<gamma> = choice_function +
  assumes \<gamma>: "A \<sqsubseteq> U \<Longrightarrow> B \<sqsubseteq> U \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> S A \<Longrightarrow> x \<in> S B \<Longrightarrow> x \<in> S (A \<union> B)"

locale sat_\<gamma>_plus = choice_function +
  assumes \<gamma>_plus: "A \<sqsubseteq> U \<Longrightarrow> B \<sqsubseteq> U \<Longrightarrow> S A \<subseteq> S (A \<union> B) \<or> S B \<subseteq> S (A \<union> B)"

(* Strong Expansion *)
locale sat_\<beta>_plus = choice_function +
  assumes \<beta>_plus: "A \<sqsubseteq> U \<Longrightarrow> B \<sqsubseteq> U \<Longrightarrow> B \<subseteq> A \<Longrightarrow> S A \<inter> B \<noteq> {} \<Longrightarrow> S B \<subseteq> S A"

sublocale sat_\<beta>_plus \<subseteq> sat_\<gamma>_plus proof
  fix A B assume au: "A \<sqsubseteq> U" and bu: "B \<sqsubseteq> U"
  hence ab: "A \<union> B \<sqsubseteq> U" by auto

  have "S (A \<union> B) \<noteq> {}" using S[of "A \<union> B"] ab by auto
  then obtain x where x: "x \<in> S (A \<union> B)" using S by auto

  have "S (A \<union> B) \<subseteq> A \<union> B" using ab S[of "A \<union> B"] by auto
  hence "x \<in> A \<or> x \<in> B" using x by auto
  thus "S A \<subseteq> S (A \<union> B) \<or> S B \<subseteq> S (A \<union> B)" using \<beta>_plus[OF ab] ab x by auto
qed

sublocale sat_\<gamma>_plus \<subseteq> sat_\<gamma> proof
  fix A B x assume "A \<sqsubseteq> U" "B \<sqsubseteq> U" "x \<in> A" "x \<in> B" "x \<in> S A" "x \<in> S B"
  thus "x \<in> S (A \<union> B)" using \<gamma>_plus by auto
qed

locale rationalizable_choice_function = choice_function +
  (* A CF is rationalizable iff it is rationalized by its  base relation *)
  assumes rationalized: "A \<sqsubseteq> U \<Longrightarrow> S A = general_preference.Max (R\<^sub>S) A"

locale sat_\<alpha>_\<gamma> = sat_\<alpha> + sat_\<gamma>

(* Sen's theorem rationalizable \<Longleftrightarrow> \<alpha> \<and> \<gamma> *)
(* Direction \<Longleftarrow> *)
sublocale sat_\<alpha>_\<gamma> \<subseteq> rationalizable_choice_function proof
  fix A assume AU: "A \<sqsubseteq> U"

  show "S A = general_preference.Max (R\<^sub>S) A" proof (rule set_eqI; rule iffI)
    fix x assume xsa: "x \<in> S A" hence xa: "x \<in> A" using S_subset by auto
    {
      fix y assume ya: "y \<in> A"
      hence xyu: "{x, y} \<sqsubseteq> U" using AU xa by blast
      have "x \<in> S A \<and> x \<in> S {x, y}" using \<alpha>[OF AU xyu xa] by (simp add: xsa insert_absorb xa ya) 
    }
    thus "x \<in> general_preference.Max (R\<^sub>S) A" using eq_base_max[OF AU xa] by auto
  next
    fix x assume xmax: "x \<in> general_preference.Max (R\<^sub>S) A"

    have xa: "x \<in> A" using general_preference.Max_def[of U "(R\<^sub>S)"] xmax AU base_complete complete_preference.Max_comp by blast

    have "finite A" using AU finite_subset finite_universe by auto 
    moreover have "A \<subseteq> A" by auto
    ultimately have "A \<sqsubseteq> U \<Longrightarrow> x \<in> S (A \<union> {x})" proof (induction rule: finite_subset_induct)
      case empty thus ?case using AU xa trivial_choice by auto
    next
      case (insert a F)
      moreover have fxu: "F \<union> {x} \<sqsubseteq> U" using AU xa insert.prems by auto
      moreover have "{x, a} \<sqsubseteq> U" using insert fxu insert.prems by auto
      moreover have "x \<in> F \<union> {x}" by auto
      moreover have "x \<in> {x, a}" by auto
      moreover have "x \<in> S (F \<union> {x})" using fxu insert.IH trivial_choice by force 
      moreover have "x \<in> S {x, a}" using AU eq_base_max insert.hyps(2) xa xmax by auto
      ultimately show ?case using \<gamma>[of "F \<union> {x}" "{x, a}" x] by (simp add: Un_commute) 
    qed
    thus "x \<in> S A" using AU xa by (simp add: insert_absorb) 
  qed
qed

(* Sen's theorem rationalizable \<Longleftrightarrow> \<alpha> \<and> \<gamma> *)
(* Direction \<Longrightarrow> *)
sublocale rationalizable_choice_function \<subseteq> sat_\<alpha>_\<gamma> proof
  fix A B x assume AU: "A \<sqsubseteq> U" and BU: "B \<sqsubseteq> U" and xa:  "x \<in> A" and xb: "x \<in> B"

  have g: "general_preference U (R\<^sub>S)" using base_complete complete_preference_def by auto

  show "x \<in> S (A \<union> B) \<Longrightarrow> x \<in> S A \<and> x \<in> S B" proof
    assume "x \<in> S (A \<union> B)"
    hence x: "x \<in> general_preference.Max (R\<^sub>S) (A \<union> B)" by (metis S_domain empty_iff rationalized)

    show "x \<in> S A" using x rationalized[OF AU] xa general_preference.Max_def[OF g] by auto 
    show "x \<in> S B" using x rationalized[OF BU] xb general_preference.Max_def[OF g] by auto 
  qed

  assume "x \<in> S A"
  hence "x \<in> general_preference.Max (R\<^sub>S) A" by (metis S_domain empty_iff rationalized)
  hence a_max: "y \<in> A \<Longrightarrow> \<not>general_preference.P (R\<^sub>S) y x" for y using general_preference.Max_def[OF g, of A] by auto

  assume "x \<in> S B"
  hence "x \<in> general_preference.Max (R\<^sub>S) B" by (metis S_domain empty_iff rationalized)
  hence b_max: "y \<in> B \<Longrightarrow> \<not>general_preference.P (R\<^sub>S) y x" for y using general_preference.Max_def[OF g, of B] by auto

  have "y \<in> B \<union> A \<Longrightarrow> \<not>general_preference.P (R\<^sub>S) y x" for y using a_max b_max by auto
  hence "x \<in> general_preference.Max (R\<^sub>S) (A \<union> B)" using general_preference.Max_def[OF g] using xb by blast
  thus "x \<in> S (A \<union> B)" by (simp add: AU BU rationalized)
qed

end