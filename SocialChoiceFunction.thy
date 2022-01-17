theory SocialChoiceFunction
  imports Main Common Base ChoiceFunction
begin

(*
  A social choice function takes the preferences of all voters and turns them into a joint choice
  function 
*)
type_synonym 'a SCF = "'a PP \<Rightarrow> 'a CF"

abbreviation invalid_scf :: "'a SCF" where "invalid_scf \<equiv> \<lambda>_. invalid_cf"
abbreviation trivial_scf :: "'a SCF" where "trivial_scf \<equiv> \<lambda>_. trivial_cf"

locale social_choice_function = social_choice_setting +
  constrains U :: "'a set"
  fixes f :: "'a SCF"
  assumes f: "preference_profile U n R\<^sub>N \<Longrightarrow> choice_function U (f R\<^sub>N)"
  assumes f_invalid: "(\<not> preference_profile U n R\<^sub>N) = (f R\<^sub>N = invalid_scf R\<^sub>N)"
begin

(* 
  Two preference profiles R and R' are related by a being reinforced for voter i, iff they are
  the same for all voters, except that for voter i alternative a could be higher ranked in R' than
  in R. The relative ordering of all other alternatives remains the same.
*)
inductive reinforced :: "nat \<Rightarrow> 'a \<Rightarrow> 'a PP relation" where "
      preference_profile U n R\<^sub>N
  \<Longrightarrow> preference_profile U n R\<^sub>N'
  \<Longrightarrow> (\<And>j x y. j \<noteq> i \<longrightarrow> R\<^sub>N j x y = R\<^sub>N' j x y)
  \<Longrightarrow> (\<And>x y.
        x \<in> U - {a}
    \<Longrightarrow> y \<in> U - {a}
    \<Longrightarrow> (
        (R\<^sub>N i x y = R\<^sub>N' i x y)
      \<and> (R\<^sub>N i a y \<longrightarrow> R\<^sub>N' i a y)
      \<and> (asymm (R\<^sub>N i) a y \<longrightarrow> asymm (R\<^sub>N' i) a y)
    )
  )
  \<Longrightarrow> reinforced i a R\<^sub>N R\<^sub>N'"
inductive_cases reinforced[elim]: "reinforced i a R\<^sub>n R\<^sub>n'"

end

locale anonymous = social_choice_function +
  (* An SCF is anonymous, if it is symmetric with respect to voters *)
  assumes anonymous: "
        f R\<^sub>N A \<noteq> invalid_cf A
    \<Longrightarrow> f R\<^sub>N' A \<noteq> invalid_cf A
    \<Longrightarrow> \<exists>\<pi>. \<forall>i \<in> N. \<forall>x \<in> A. \<forall>y \<in> A. R\<^sub>N i x y = R\<^sub>N' (\<pi> i) x y
    \<Longrightarrow> f R\<^sub>N A = f R\<^sub>N' A
  "

locale neutral = social_choice_function +
  (* 
    An SCF is neutral, if it is symmetric with respect to alternatives and is independent of
    alternatives not contained in the feasible set it is called with
  *)
  assumes neutral: "
        f R\<^sub>N A \<noteq> invalid_cf A
    \<Longrightarrow> f R\<^sub>N B \<noteq> invalid_cf B
    \<Longrightarrow> \<exists>\<pi>. \<forall>i \<in> N. \<forall>x \<in> A. \<forall>y \<in> A.
          \<pi> x \<in> B
        \<and> \<pi> y \<in> B
        \<and> R\<^sub>N i x y = R\<^sub>N' i (\<pi> x) (\<pi> y)
    \<Longrightarrow> f R\<^sub>N A = f R\<^sub>N' B
  "

locale pareto_optimal = social_choice_function +
  (* 
    An SCF is pareto optimal, if it never chooses alternatives such that there is another
    alternative that every voter prefers to it
  *)
  assumes pareto: "
        f R\<^sub>N A \<noteq> invalid_cf A
    \<Longrightarrow> x \<in> f R\<^sub>N A
    \<Longrightarrow> y \<in> A
    \<Longrightarrow> \<exists>i. R\<^sub>N i x y
  "

locale resolute = social_choice_function +
  (* An SCF is resolute, if it never has any ties, i.e. the choice set is always a singleton *)
  assumes resolute: "f R\<^sub>N A \<noteq> invalid_cf A \<Longrightarrow> card (f R\<^sub>N A) = 1"

locale monotonic = social_choice_function +
  (* An SCF is monotonic, if a chosen alternative is still chosen when it is reinforced *)
  assumes monotonic: "
        f R\<^sub>N A \<noteq> invalid_cf A
    \<Longrightarrow> f R\<^sub>N' A \<noteq> invalid_cf A
    \<Longrightarrow> \<exists>i \<in> N. reinforced i a R\<^sub>N R\<^sub>N'
    \<Longrightarrow> a \<in> f R\<^sub>N A
    \<Longrightarrow> a \<in> f R\<^sub>N' A
  "

locale positive_responsive = social_choice_function +
  (* 
    An SCF is positive responsive, if, when a is chosen, then a is chosen uniquely when properly
    reinforced 
  *)
  assumes positive_responsive: "
        f R\<^sub>N A \<noteq> invalid_cf A
    \<Longrightarrow> f R\<^sub>N' A \<noteq> invalid_cf A
    \<Longrightarrow> \<exists>i \<in> N. reinforced i a R\<^sub>N R\<^sub>N' \<and> (\<exists>x \<in> A. \<exists>y \<in> A. R\<^sub>N i x y \<noteq> R\<^sub>N' i x y)
    \<Longrightarrow> a \<in> f R\<^sub>N A
    \<Longrightarrow> f R\<^sub>N' A = {a}
  "
end