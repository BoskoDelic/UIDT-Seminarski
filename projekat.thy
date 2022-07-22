theory projekat
  imports Complex_Main
begin

(* 
 uvodim
 p = sqrt a + sqrt b
 q = sqrt a - sqrt b
*)
fun p :: "real \<Rightarrow> real \<Rightarrow> real" where
"p a b = sqrt a + sqrt b"

fun q :: "real \<Rightarrow> real \<Rightarrow> real" where
"q a b = sqrt a - sqrt b"


(*
 pokazujem p * q = a - b, razlika kvadrata 
*)
lemma razlika_kvadrata_pq:
  fixes a b c :: real
  assumes "a > 0" "b > 0"
  shows "(p a b) * (q a b) = a - b"
  using assms
proof -
  have "(p a b) * (q a b) = (sqrt a + sqrt b) * (sqrt a - sqrt b)" by auto
  also have "... = sqrt a * sqrt a - sqrt a * sqrt b + sqrt b * sqrt a - sqrt b * sqrt b" by (smt (verit, ccfv_SIG) distrib_left mult.commute)
  also have "... = sqrt a * sqrt a - sqrt b * sqrt b" by auto
  also have "... = a - b" using assms by auto
  finally show ?thesis by auto
qed


(*
 pokazujem (a + b - c - a) / (sqrt(a + b - c) + sqrt a) \<le> (b - c) / (sqrt b + sqrt c)
*)
lemma nejednakost_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "(a + b - c - a) / (sqrt(a + b - c) + sqrt a) \<le> (b - c) / (sqrt b + sqrt c)"
  by (smt (verit, ccfv_SIG) assms(3) assms(4) assms(5) frac_le real_sqrt_gt_0_iff real_sqrt_le_mono)

(*
 transformisem levu stranu nejednakosti korenova
 (a + b - c - a) / (sqrt(a + b - c) + sqrt a) = sqrt(a + b - c) - sqrt a
*)
lemma L_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a = (a + b - c - a) / (sqrt(a + b - c) + sqrt a)"
  by (smt (verit, del_insts) assms(1) assms(6) nonzero_mult_div_cancel_left p.elims q.elims razlika_kvadrata_pq real_sqrt_le_0_iff)

(*
 transformisem desnu stranu nejednakosti korenova
 (b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c
*)
lemma D_veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "(b - c) / (sqrt b + sqrt c) = sqrt b - sqrt c"
  by (smt (verit, ccfv_threshold) assms(2) assms(3) nonzero_mult_div_cancel_left p.elims q.elims razlika_kvadrata_pq real_sqrt_ge_zero real_sqrt_le_iff)

(*
 povezujem levu i desnu transformisanu stranu u nejednakost
 sqrt(a + b - c) - sqrt a \<le> sqrt b - sqrt c
*)
lemma veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt a \<le> sqrt b - sqrt c"
  using assms
  using D_veza_korenova L_veza_korenova nejednakost_korenova by force

(*
 pokazujem da je veza_korenova \<le> 1
*)
lemma manje_od_jedan:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt (a + b - c) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 1"
  using assms
  by (smt (verit) divide_le_eq_1 real_sqrt_gt_0_iff veza_korenova)

(*
 posto treba da pokazemo da je konacna nejednakost \<le> 3, a upravo smo pokazali da je
 jedan od njenih sabiraka \<le> 1, onda za ostala dva sabirka treba pokazati da su \<le> 2
*)

(*
 uvodim p i q u preostala 2 sabirka
*)
lemma uvedi_pq:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a) + sqrt(c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt(c - p a b * q a b) / (sqrt c - q a b) + sqrt(c + p a b * q a b) / (sqrt c + q a b)"
  using assms
  by (smt (verit, del_insts) q.simps razlika_kvadrata_pq)

(*
 pokazujem da su preostali sabirci manji od 2
  TODO
*)

lemma manje_od_dva:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(c - p a b * q a b) / (sqrt c - q a b) + sqrt(c + p a b * q a b) / (sqrt c + q a b) \<le> 2"
  using assms
  sorry



(*
 dokaz konacne nejednakosti
*)
lemma final_theorem:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b" (* posto a, b, c stranice trougla *)
  shows "(sqrt(b + c - a)) / (sqrt (b) + sqrt (c) - sqrt (a)) + 
sqrt((c + a - b)) / (sqrt (c) + sqrt (a) - sqrt (b)) +
(sqrt(a + b - c)) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 3"
  using assms
  sorry



end