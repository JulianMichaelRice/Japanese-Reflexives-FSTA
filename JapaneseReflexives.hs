------------------------------------------------------------------------
-- Representing Japanese Reflexives Through Finite State Tree Automaton
-- Julian Michael Rice | March 21st, 2019
-- UCLA | Computational Linguistics I
------------------------------------------------------------------------
module JapaneseReflexives where
import NewTreeGrammars
-----------------------------------------------------------------

data AnaphoraStatus = Normal | 
                     Zibun | ZibunZishin | Mizukara | 
                     TypeAOK | TypeBOK | 
                     LicR 
     deriving (Eq,Ord,Show)

data Transitions = MergeJP |
                   Antecedent 
     deriving (Eq, Ord, Show)

fsta_jp :: Automaton AnaphoraStatus String Gam1 Transitions
fsta_jp = ( -- Ending States
            [Normal, TypeAOK, TypeBOK],
            -- Nullary Transitions
            [(s, Normal) | s <- ["wo","ga","koe","kikoe-ta","omot-ta","to","no","hihan-shita","wa"]] ++
            [(s, TypeAOK) | s <- ["Yukino"]] ++ -- Example for long distance or singular only antecedent
            [(s, TypeBOK) | s <- ["Kuribo"]] ++ -- Example for short distance and the latter antecedent
            [(s, LicR) | s <- ["R-OK"]] ++
            [(s, Zibun) | s <- ["zibun", "zibun-no"]] ++
            [(s, ZibunZishin) | s <- ["zibun-zishin", "zibun-zishin-no"]] ++
            [(s, Mizukara) | s <- ["mizukara", "mizukara-no"]],
            -- Unary Transitions
            [],
            -- Binary Transitions
            [(Normal, Normal, MergeJP, Normal),
             (Normal, Zibun, MergeJP, Zibun),

             -- Local Antecedent Rules
             (TypeAOK, Zibun, MergeJP, Normal),
             (TypeAOK, Mizukara, MergeJP, Normal),
             (TypeAOK, Normal, MergeJP, Normal),

             -- Non-local Antecedent Rules
             (TypeBOK, Zibun, MergeJP, Normal),
             (TypeBOK, Mizukara, MergeJP, Normal),
             (TypeBOK, ZibunZishin, MergeJP, Normal),
             (TypeBOK, Normal, MergeJP, Normal),

             -- Unsatisfied Reflexive (First Blood!) Rules
             (Normal, Zibun, Antecedent, Zibun), 
             (Normal, Mizukara, Antecedent, Zibun),
             (Normal, ZibunZishin, Antecedent, Zibun),

             -- Search for Antecedent Rules
             (Zibun, Normal, MergeJP, Zibun),
             (ZibunZishin, Normal, MergeJP, ZibunZishin),
             (Mizukara, Normal, MergeJP, Mizukara), 

             -- Finishing State
             (LicR, Normal, MergeJP, Normal)]
          )

tree_jp1a :: Tree String Gam1 Transitions
tree_jp1a = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino")  (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "zibun") (Binary MergeJP (Leaf "wo") (Leaf "hihan-shita")))))

tree_jp1b :: Tree String Gam1 Transitions
tree_jp1b = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "zibun")  (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "Yukino") (Binary MergeJP (Leaf "wo") (Leaf "hihan-shita")))))

tree_jp2 :: Tree String Gam1 Transitions
tree_jp2 = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino")  (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "zibun-zishin") (Binary MergeJP (Leaf "wo") (Leaf "hihan-shita")))))

tree_jp3 :: Tree String Gam1 Transitions
tree_jp3 = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino")  (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "mizukara") (Binary MergeJP (Leaf "wo") (Leaf "hihan-shita")))))

tree_jp4 :: Tree String Gam1 Transitions
tree_jp4 = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino") (Binary MergeJP (Leaf "wa") (Binary MergeJP (Leaf "Kuribo") (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "zibun-no") (Binary MergeJP (Leaf "koe") (Binary MergeJP (Leaf "ga") (Binary MergeJP (Leaf "kikoe-ta") (Binary MergeJP (Leaf "to") (Leaf "omot-ta"))))))))))

tree_jp5 :: Tree String Gam1 Transitions
tree_jp5 = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino") (Binary MergeJP (Leaf "wa") (Binary MergeJP (Leaf "Kuribo") (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "zibun-zishin-no") (Binary MergeJP (Leaf "koe") (Binary MergeJP (Leaf "ga") (Binary MergeJP (Leaf "kikoe-ta") (Binary MergeJP (Leaf "to") (Leaf "omot-ta"))))))))))

tree_jp6 :: Tree String Gam1 Transitions
tree_jp6 = Binary MergeJP (Leaf "R-OK") (Binary MergeJP (Leaf "Yukino") (Binary MergeJP (Leaf "wa") (Binary MergeJP (Leaf "Kuribo") (Binary Antecedent (Leaf "ga") (Binary MergeJP (Leaf "mizukara-no") (Binary MergeJP (Leaf "koe") (Binary MergeJP (Leaf "ga") (Binary MergeJP (Leaf "kikoe-ta") (Binary MergeJP (Leaf "to") (Leaf "omot-ta"))))))))))

insideCheck :: (Ord st, Eq sy0, Eq sy1, Eq sy2) => Automaton st sy0 sy1 sy2 -> Tree sy0 sy1 sy2 -> st -> Bool
insideCheck fsta tree state =
    let (ends, nullaries, unaries, binaries) = fsta in
    let states = allStates fsta in
    case tree of
        Leaf x -> elem state [q | (y, q) <- nullaries, y == x]
        Unary x t -> or [insideCheck fsta t q | (q', y, q) <- unaries, y == x, q' == state]
        Binary x t1 t2 -> or [(and [(insideCheck fsta t1 q1 && insideCheck fsta t2 q2)]) | (q1, q2, y, q) <- binaries, y == x, q == state]