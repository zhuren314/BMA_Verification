theory BMA_Veri
  imports (* Refine_Imperative_HOL.IICF*)
    "HOL-Library.Sublist"
begin

fun bmSearch :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "bmSearch _ [] = False" |
  "bmSearch [] _ = True" |
  "bmSearch (xs#zs) (ys#y) = undefined"


fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sublist_at "

(*fun first_occurrence *)
fun last_occurrence :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "last_occurrence [] _ = None"
| "last_occurrence (x # xs) y = (if x = y then Some 0 else map_option Suc (last_occurrence xs y))"

fun bad_character_rule :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
  "bad_character_rule pattern j mismatch_char =
    (case last_occurrence (take j pattern) mismatch_char of
      None \<Rightarrow> j + 1
    | Some k \<Rightarrow> j - k
    )"

fun good_suffix_rule :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "good_suffix_rule pattern suffix =
    (let m = length pattern;
         n = length suffix;
         suff_shift = map (\<lambda>i. m) [0..<m];
         z = suffix_shift pattern
     in
       (let f = index (map (op ! n) (filter (\<lambda>i. z ! i = m - 1) [0..<n]))
    )"

fun boyer_moore_search :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "boyer_moore_search text pattern =
    (let n = length text; m = length pattern in
      if m = 0 then  0
      else if m > n then None
      else
        let i = ref 0; j = ref (m - 1) in
        while !i \<le> n - m do
          let j = ref (m - 1);
          while !j \<ge> 0 \<and> pattern !(!j) = text !(!i + !j) do j := !j - 1 done;
          if !j < 0 then (Some !i)
          else i := !i + max 1 (!j - bad_character_rule pattern !j (text !(!i + !j)))
        done;
        None
    )"

end