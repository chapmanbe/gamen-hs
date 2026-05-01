-- | Render Kripke frames and models as Graphviz @dot@ source.
--
-- The notebook build pipeline pipes the output through
-- @dot -Tsvg@ to produce a figure that gets embedded in the
-- rendered Markdown. The functions here are pure: they take a
-- 'Frame' or 'Model' and return a 'String' of @dot@ source. Any
-- I/O (writing the file, calling @dot@) is the caller's job.
--
-- Conventions:
--
-- * Worlds are circular nodes labelled with the world name.
-- * For 'Model', each node label also lists the atoms holding at
--   that world, on a second line.
-- * Edges are directed (the accessibility relation is binary, not
--   necessarily symmetric).
-- * Default layout is left-to-right (@rankdir=LR@); override by
--   editing the produced source.
module Gamen.Visualize
  ( toGraphviz
  , toGraphvizModel
  ) where

import Data.List (intercalate, sort)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Gamen.Formula (Atom (..))
import Gamen.Kripke

-- | Render a 'Frame' (just structure, no valuation) as @dot@ source.
toGraphviz :: Frame -> String
toGraphviz fr = render (sort (Set.toList (worlds fr))) edges plainNode
  where
    edges =
      [ (w, u)
      | (w, us) <- Map.toAscList (relation fr)
      , u       <- Set.toAscList us
      ]
    plainNode w = w ++ " [label=\"" ++ w ++ "\"];"

-- | Render a 'Model' as @dot@ source. Each world's label includes the
-- atoms holding there, separated from the world name by a literal
-- newline (rendered as a line break by Graphviz).
toGraphvizModel :: Model -> String
toGraphvizModel m =
    render (sort (Set.toList (worlds (frame m)))) edges modelNode
  where
    edges =
      [ (w, u)
      | (w, us) <- Map.toAscList (relation (frame m))
      , u       <- Set.toAscList us
      ]

    -- For each world, pick out the atoms it satisfies.
    atomsAt w = sort
      [ atomName a
      | (a, ws) <- Map.toList (valuation m)
      , Set.member w ws
      ]

    modelNode w =
      let as = atomsAt w
          atomLine
            | null as   = ""
            | otherwise = "\\n" ++ intercalate ", " as
      in w ++ " [label=\"" ++ w ++ atomLine ++ "\"];"

-- | Common @dot@ scaffolding shared by 'toGraphviz' and
-- 'toGraphvizModel'. Caller supplies the sorted node list, the
-- edge list, and a function that produces the @dot@ statement for
-- each node.
render :: [World] -> [(World, World)] -> (World -> String) -> String
render nodes edges nodeStmt = unlines $
  [ "digraph K {"
  , "  rankdir=LR;"
  , "  bgcolor=\"transparent\";"
  , "  node [shape=circle, fontname=\"et-book, Palatino, serif\","
       ++ " fontsize=12, color=\"#111\", fontcolor=\"#111\"];"
  , "  edge [color=\"#555\", arrowsize=0.7];"
  ]
  ++ [ "  " ++ nodeStmt w | w <- nodes ]
  ++ [ "  " ++ src ++ " -> " ++ dst ++ ";" | (src, dst) <- edges ]
  ++ [ "}" ]
