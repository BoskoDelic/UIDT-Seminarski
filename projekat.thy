theory projekat
  imports Complex_Main
begin

(* definisati p i q *)

lemma veza_korenova:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt(a + b - c) - sqrt(a) = sqrt(b) - sqrt(c)"
  sorry


lemma manje_od_jedan:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b"
  shows "sqrt (a + b - c) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 1"
  sorry


lemma final_theorem:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a \<ge> b" "b \<ge> c" "a + b > c" "b + c > a" "a + c > b" (* posto a, b, c stranice trougla *)
  shows "(sqrt(b + c - a)) / (sqrt (b) + sqrt (c) - sqrt (a)) + 
sqrt((c + a - b)) / (sqrt (c) + sqrt (a) - sqrt (b)) +
(sqrt(a + b - c)) / (sqrt (a) + sqrt (b) - sqrt (c)) \<le> 3"
  sorry



end