theory BMA_Veri
  imports "HOL-Library.Sublist"
begin

fun bmSearch :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "bmSearch _ [] = False" |
  "bmSearch [] _ = True" |
  "bmSearch (xs#zs) (ys#y) = undefined"

(*fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sublist_at "*)

fun first_occurrence :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "first_occurrence [] _ = None" |
  "first_occurrence (x # xs) y = (if x = y then Some 0 else map_option Suc (first_occurrence xs y))"

fun last_occurrence :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "last_occurrence [] _ = None" |
  "last_occurrence xs y =
   (let l = length xs
    in 
    map_option (\<lambda>n. l - n - 1) (first_occurrence (rev xs) y))"

(* String -> [(Char, Int)]*)
fun generate_bad_char_table :: "string \<Rightarrow> (char \<times> nat) list" where
  "generate_bad_char_table pattern = rev (zip pattern (rev (List.upt 0 (length pattern - 1))))"

fun is_suffix :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "is_suffix pattern i = list_all (\<lambda>(x, y). x = y) (zip (drop i pattern) (rev (take (length pattern - i) pattern)))"

(* String -> [Int]*)
fun generate_good_suffix_table :: "string \<Rightarrow> nat list" where
  "generate_good_suffix_table pattern = rev (concat (map (\<lambda>i. filter (\<lambda>j. is_suffix pattern j) (List.upt 1 (length pattern - 1))) (List.upt 1 (length pattern - 1))))"


fun bad_character_rule :: "string \<Rightarrow> nat \<Rightarrow> char \<Rightarrow> nat" where
(*if we fand Bad_Cha: schift to right = index of bad_cha -  Rightmost index of BC at pattern
  if pattern dosent contain BC, then -1 as Rightmostt index
  e.g. "A SIMPLE" P is BadCha
      "EXAMPLE"
  to   "A SIMPLE"  alignment 'P'
     \<Rightarrow> "EXAMPLE" *)
  "bad_character_rule pattern j mismatch_char =
    (case last_occurrence (take j pattern) mismatch_char of
      None \<Rightarrow> j + 1 |
      Some k \<Rightarrow> j - k
    )"

fun good_suffix_rule :: "string \<Rightarrow> string \<Rightarrow> nat" where
(* If there is a mismatch: shift = GoodSuff index at pattern - Last occurrence index of GS in pattern (上一次出现的索引)
 If GS does not occur in pattern again, then this will be -1 *)
  "good_suffix_rule pattern suffix =
    (let m = length pattern;
         n = length suffix;
         z = generate_good_suffix_table pattern
     in
       (let f = hd (filter (\<lambda>i. z ! i = m - 1) (List.upt 0 (length z - 1)))
        in
        if f = 0 then m
        else f - m + 1
       )
    )"


fun boyer_moore_search :: "string \<Rightarrow> string \<Rightarrow> nat option" where

  "boyer_moore_search text pattern =
    (let n = length text; m = length pattern in
      if m = 0 then Some 0
      else if m > n then None
      else
        let bc_table = generate_bad_char_table pattern;
            gs_table = generate_good_suffix_table pattern;
            i = ref (m - 1);
            j = ref (m - 1)
        in
        while !i < n do
          if text !(!i) = pattern !(!j) then
            (if !j = 0 then Some !i
            else (i := !i - 1; j := !j - 1))
          else
            (let bc_shift = case map_of bc_table (text !(!i)) of None \<Rightarrow> m | Some k \<Rightarrow> !j - k;
                 gs_shift = if !j = m - 1 then 1 else good_suffix_rule pattern (drop (!j + 1) pattern)
             in
             (i := !i + max bc_shift gs_shift;
              j := m - 1))
        done;
        None
    )"


value "boyer_moore_search ''ABAAABCD'' ''ABC''"

end
