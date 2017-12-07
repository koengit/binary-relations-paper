module Anal where

import Data.List
import qualified Data.Map as M

props = words
  "reflexive euclidean antisymmetric transitive asymmetric total symmetric coreflexive"

ann "euclidean"  = "right_euclidean"
ann "asymmetric" = "total"
ann p            = p

rels =
  [ ("equivalence relations", ["transitive","reflexive","symmetric"])
  , ("partial equivalence relations", ["transitive", "symmetric"])
  , ("(strict) total orders", ["total","antisymmetric","transitive"])
  , ("reflexive, transitive relations (excluding the above)", ["transitive","reflexive"])
  , ("transitive relations (excluding the above)", ["transitive"])
  ]

main =
  do s <- readFile "propertytable"
     let tab = M.toList $ M.fromListWith union $
               [ ((file,rel),[prop])
               | l <- lines s
               , let [file,list] = words (fiximpl l)
               , (rel',props') <- parse (words (map trans list))
               , let (rel,op) = fluff rel'
               , prop <- map (++op) props'
               , not ("=>" `isPrefixOf` prop)
               ]
     putStrLn ("% found " ++ show (length tab) ++ " relations")
     
     s <- readFile "lagom_stora_v7.0_with_status"
     let stat = M.fromList
                [ (file,st)
                | l <- lines s
                , let [file,st] = words l
                ]
         
         isSAT file =
           case M.lookup file stat of
             Just "CounterSatisfiable" -> True
             Just "Open" -> False
             Just "Satisfiable" -> True
             Just "Theorem" -> False
             Just "Unknown" -> False
             Just "Unsatisfiable" -> False
             x -> error (show (file,x))

     putStrLn ("% found " ++ show (M.size stat) ++ " problem files")
  
     putStrLn ""
     putStrLn ("% TABLE 1")
     sequence_
       [ putStrLn (show n ++ " & " ++ prop ++ " \\\\")
       | (n,prop) <- reverse $ sort
           [ ( length [ (file,rel)
                      | ((file,rel),ps) <- tab
                      , any (ann prop `isPrefixOf`) ps
                      ]
             , prop
             )
           | prop <- props 
           ]
       ]
     
     let rtypes = M.fromListWith (++)
                  [ (rtype,[(file,rel)])
                  | ((file,rel),props) <- tab
                  , Just rtype <- [reltype props]
                  ]

     putStrLn ""
     putStrLn ("% TABLE 2")
     sequence_
       [ putStrLn ( show (length [ r | (file,r) <- rs, not (isSAT file) ])
                 ++ "+"
                 ++ show (length [ r | (file,r) <- rs, isSAT file ])
                 ++ " & "
                 ++ rtype
                 ++ " \\\\"
                  )
       | (rtype, _) <- rels
       , Just rs <- [M.lookup rtype rtypes]
       ]
 where
  fiximpl ('=':'>':' ':s) = "=>_" ++ fiximpl s
  fiximpl (c:s)           = c: fiximpl s
  fiximpl ""              = ""
  
  trans '[' = ' '
  trans ']' = ' '
  trans ',' = ' '
  trans ')' = ' '
  trans c   = c
 
  parse (('(':rel):props) =
      (rel,takeWhile ((/='(').head) props)
    : parse (dropWhile ((/='(').head) props)
 
  parse [] =
    []

  fluff s = (takeWhile notOp s, filter keep (dropWhile notOp s))
   where
    notOp '+' = False
    notOp '-' = False
    notOp '<' = False
    notOp '>' = False
    notOp _   = True
    
    keep '-' = True
    keep '<' = True
    keep _   = False

reltype props =
  case [ rtype
       | (rtype,props') <- rels
       , op <- ["","-","-<","<"]
       , all (\p -> (p++op) `elem` props) props'
       ] of
    rtype:_ -> Just rtype
    _       -> Nothing

