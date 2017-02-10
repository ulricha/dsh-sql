module Database.DSH.Backend.Sql.MultisetAlgebra.Dot
    ( renderMADot
    ) where

import           Data.List
import qualified Data.List.NonEmpty                            as N
import           Prelude                                       hiding ((<$>))

import           Text.PrettyPrint.ANSI.Leijen

import qualified Database.Algebra.Dag                          as Dag
import           Database.Algebra.Dag.Common                   as C

import qualified Database.DSH.Common.Lang                      as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.VectorLang                ()

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderLambda :: Pretty e => e -> Doc
renderLambda e = text "\\x." <> pretty e

renderId :: AlgNode -> Doc
renderId n = text "id:" <+> int n

labelDoc :: AlgNode -> String -> Doc -> Doc
labelDoc nodeId opName arg = renderId nodeId <$> (text opName <> arg)

renderLabel :: AlgNode -> String -> Doc
renderLabel nodeId opName = labelDoc nodeId opName empty

renderLabelArg :: AlgNode -> String -> Doc -> Doc
renderLabelArg nodeId opName arg = labelDoc nodeId opName (braces arg)

-- | Create the node label from an operator description
opDotLabel :: AlgNode -> MA -> Doc
opDotLabel i (UnOp (Project e) _) = renderLabelArg i "project" (renderLambda e)
opDotLabel i (UnOp (Select e) _) = renderLabelArg i "select" (renderLambda e)
opDotLabel i (UnOp (Distinct _) _) = renderLabel i "distinct"
opDotLabel i (UnOp (GroupAggr (g, (L.NE as))) _) = renderLabelArg i "groupaggr" (renderLambda g <+> bracketList pretty (N.toList as))
opDotLabel i (UnOp (RowNumPart (p,o)) _) = renderLabelArg i "rownum" (renderLambda p <> comma <> renderLambda o)
opDotLabel i (NullaryOp (Lit segs)) = renderLabelArg i "lit" (pretty segs)
opDotLabel i (NullaryOp (Table (n, _, _))) = renderLabelArg i "table" (text n)
opDotLabel i (BinOp (ThetaJoin p) _ _) =
  renderLabelArg i "thetajoin" (pretty p)
opDotLabel i (BinOp (LeftOuterJoin (p,d,r)) _ _) =
  renderLabelArg i "louterjoin" ((pretty p) <> comma <> pretty d <> comma <> renderLambda r)
opDotLabel i (BinOp (GroupJoin (p, L.NE as)) _ _) =
  renderLabelArg i "groupjoin" ((pretty p) <> comma <> bracketList pretty (N.toList as))
opDotLabel i (BinOp (CartProduct _) _ _) =
  renderLabel i "cartproduct"
opDotLabel i (BinOp (SemiJoin p) _ _) =
  renderLabelArg i "semijoin" (pretty p)
opDotLabel i (BinOp (AntiJoin p) _ _) =
  renderLabelArg i "antijoin" (pretty p)
opDotLabel i (BinOp (Union _) _ _) =
  renderLabel i "union"
opDotLabel _ TerOp{} = error "no ternary MA operators"

opDotColor :: MA -> DotColor
opDotColor (UnOp (RowNumPart _) _)       = DCCrimson
opDotColor (UnOp (Distinct _) _)         = DCTan
opDotColor (UnOp (GroupAggr (_, _)) _)   = DCTomato
opDotColor (BinOp (ThetaJoin _) _ _)     = DCGreen
opDotColor (BinOp (LeftOuterJoin _) _ _) = DCSeaGreen
opDotColor (BinOp (SemiJoin _) _ _)      = DCYellowGreen
opDotColor (BinOp (AntiJoin _) _ _)      = DCYellowGreen
opDotColor (UnOp (Select _) _)           = DCDodgerBlue
opDotColor (UnOp (Project _) _)          = DCLightSkyBlue
opDotColor (BinOp (Union _) _ _)         = DCHotPink
opDotColor _                             = DCGray

-- Dot colors
data DotColor = DCTomato
              | DCSalmon
              | DCGray
              | DimDCGray
              | DCGold
              | DCTan
              | DCRed
              | DCCrimson
              | DCGreen
              | DCSeaGreen
              | DCYellowGreen
              | DCSienna
              | DCBeige
              | DCDodgerBlue
              | DCLightSkyBlue
              | DCHotPink

renderColor :: DotColor -> Doc
renderColor DCTomato       = text "tomato"
renderColor DCSalmon       = text "salmon"
renderColor DCGray         = text "gray"
renderColor DimDCGray      = text "dimgray"
renderColor DCGold         = text "gold"
renderColor DCTan          = text "tan"
renderColor DCRed          = text "red"
renderColor DCCrimson      = text "crimson"
renderColor DCGreen        = text "green"
renderColor DCSeaGreen     = text "seagreen"
renderColor DCYellowGreen  = text "yellowgreen"
renderColor DCSienna       = text "sienna"
renderColor DCBeige        = text "beige"
renderColor DCDodgerBlue   = text "dodgerblue"
renderColor DCLightSkyBlue = text "lightskyblue"
renderColor DCHotPink      = text "hotpink"

escapeLabel :: String -> String
escapeLabel s = concatMap escapeChar s

escapeChar :: Char -> [Char]
escapeChar '\n' = ['\\', 'n']
escapeChar '\\' = ['\\', '\\']
escapeChar '\"' = ['\\', '"']
escapeChar c = [c]

-- Type of Dot style options
data DotStyle = Dashed

-- label of Dot nodes
type DotLabel = String

-- id of Dot nodes
type DotNodeID = Int

-- Type of Dot nodes
data DotNode = DotNode DotNodeID DotLabel DotColor (Maybe DotStyle)

-- Type of Dot edges
data DotEdge = DotEdge DotNodeID DotNodeID

-- Generate the preamble of a Dot file
preamble :: Doc
preamble = graphAttributes <$> nodeAttributes
    where nodeAttributes = text "node" <+> (brackets $ text "style=filled" <> comma <+> text "shape=box") <> semi
          graphAttributes = text "ordering=out;"

renderDotNode :: DotNode -> Doc
renderDotNode (DotNode n l c s) =
    int n
    <+> (brackets $ (((text "label=") <> (dquotes $ text l))
                     <> comma
                     <+> (text "color=") <> (renderColor c)
                     <> styleDoc))
    <> semi
  where
    styleDoc = case s of
                  Just Dashed -> comma <+> text "style=dashed"
                  Nothing     -> empty

renderDotEdge :: DotEdge -> Doc
renderDotEdge (DotEdge u v) = int u <+> text "->" <+> int v <> semi

-- | Render a Dot document from the preamble, nodes and edges
renderDot :: [DotNode] -> [DotEdge] -> Doc
renderDot ns es = text "digraph" <> (braces $ preamble <$> nodeSection <$> edgeSection)
  where
    nodeSection = vcat $ map renderDotNode ns
    edgeSection = vcat $ map renderDotEdge es

constructDotNode :: [AlgNode] -> (AlgNode, MA) -> DotNode
constructDotNode rootNodes (n, op) =
    if elem n rootNodes then
        DotNode n l c (Just Dashed)
    else
        DotNode n l c Nothing
  where
    l = escapeLabel $ pp $ opDotLabel n op
    c = opDotColor op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
-- FIXME no apparent reason to use topological ordering here
extractGraphStructure :: Dag.AlgebraDag MA -> ([(AlgNode, MA)], [(AlgNode, AlgNode)])
extractGraphStructure d = (operators, childs)
  where
    nodes     = Dag.topsort d
    operators = zip nodes $ map (flip Dag.operator d) nodes
    childs    = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render a multiset algebra plan into a dot file (GraphViz).
renderMADot :: [AlgNode] -> NodeMap MA -> String
renderMADot roots m = pp $ renderDot dotNodes dotEdges
  where
    (opLabels, edges) = extractGraphStructure d
    d                 = Dag.mkDag m roots
    dotNodes          = map (constructDotNode roots) opLabels
    dotEdges          = map constructDotEdge edges
