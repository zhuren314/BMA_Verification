theory BMA_Veri
  imports  "HOL-Library.Sublist"
begin

fun bmSearch :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "bmSearch _ [] = False" |
  "bmSearch [] _ = True" |
  "bmSearch (xs#zs) (ys#y) = undefined"


(*fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sublist_at "*)

(*fun first_occurrence *)
fun first_occurrence :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "first_occurrence [] _ = None"
| "first_occurrence (x # xs) y = (if x = y then Some 0 else map_option Suc (first_occurrence xs y))"

(*fun last_occurrence TODO *)
fun last_occurrence :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "last_occurrence [] _ = None"
| "last_occurrence (?xs # x) y = (if x = y then Some 0 else map_option Suc (last_occurrence xs y))"

fun bad_character_rule :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
(*if we fand Bad_Cha: schift to right = index of bad_cha -  Rightmost index of BC at pattern
  if pattern dosent contain BC, then -1 as Rightmostt index
  e.g. "A SIMPLE" P is BadCha
      "EXAMPLE"
  to   "A SIMPLE"  alignment 'P'
     \<Rightarrow> "EXAMPLE" *)
  "bad_character_rule pattern j mismatch_char =
    (case last_occurrence (take j pattern) mismatch_char of
      None \<Rightarrow> j + 1
    | Some k \<Rightarrow> j - k
    )"

fun good_suffix_rule :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
(*if mismatch: schift = GoodSuff index at pattern - GS last occur at pattern(shang yi ci)
 if GS dont occur in pattern again, then this -1 as num  *)
  "good_suffix_rule pattern suffix =
    (let m = length pattern;
         n = length suffix;
         suff_shift = map (\<lambda>i. m) [0..<m];
         z = suffix_shift pattern
     in
       (let f = index (map (op ! n) (filter (\<lambda>i. z ! i = m - 1) [0..<n]))
    )"

(* String -> [(Char, Int)]*)
fun generate_bad_char_table :: "string \<Rightarrow> (char \<times> nat) list" where
  "generate_bad_char_table pattern = rev (zip pattern (rev (upt (length pattern - 1) 0)))"

(* String -> [Int]*)
fun generate_good_suffix_table :: "string \<Rightarrow> nat list" where
  "generate_good_suffix_table pattern = rev (concat (map (\<lambda>i. filter (\<lambda>j. is_suffix pattern j) (rev (take i (upt 1 (length pattern - 1))))) (rev (upt 1 (length pattern - 1)))))"

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
-- test case
value "boyer_moore_search ''ABAAABCD'' ''ABC''"

end