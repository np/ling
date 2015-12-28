module MiniC.Skel where

-- Haskell module generated by the BNF converter

import MiniC.Abs
import MiniC.ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transIdent :: Ident -> Result
transIdent x = case x of
  Ident string -> failure x
transPrg :: Prg -> Result
transPrg x = case x of
  PPrg defs -> failure x
transDec :: Dec -> Result
transDec x = case x of
  Dec qtyp ident arrs -> failure x
transDef :: Def -> Result
transDef x = case x of
  DDef dec decs stms -> failure x
  DSig dec decs -> failure x
  DDec dec -> failure x
transTyp :: Typ -> Result
transTyp x = case x of
  TInt -> failure x
  TDouble -> failure x
  TChar -> failure x
  TStr flds -> failure x
  TUni flds -> failure x
  TEnum enms -> failure x
  TVoid -> failure x
  TPtr typ -> failure x
transEnm :: Enm -> Result
transEnm x = case x of
  EEnm ident -> failure x
  ECst ident exp -> failure x
transFld :: Fld -> Result
transFld x = case x of
  FFld typ ident arrs -> failure x
transArr :: Arr -> Result
transArr x = case x of
  AArr exp -> failure x
transQTyp :: QTyp -> Result
transQTyp x = case x of
  QTyp qual typ -> failure x
transQual :: Qual -> Result
transQual x = case x of
  NoQual -> failure x
  QConst -> failure x
transStm :: Stm -> Result
transStm x = case x of
  SDec dec init -> failure x
  SPut lval exp -> failure x
  SFor stm1 exp stm2 stms -> failure x
  SSwi exp branchs -> failure x
transBranch :: Branch -> Result
transBranch x = case x of
  Case exp stms -> failure x
transInit :: Init -> Result
transInit x = case x of
  NoInit -> failure x
  SoInit exp -> failure x
transLiteral :: Literal -> Result
transLiteral x = case x of
  LInteger integer -> failure x
  LDouble double -> failure x
  LString string -> failure x
  LChar char -> failure x
transUOp :: UOp -> Result
transUOp x = case x of
  UAmp -> failure x
  UPtr -> failure x
  UPlus -> failure x
  UMinus -> failure x
  UTilde -> failure x
  UBang -> failure x
transExp :: Exp -> Result
transExp x = case x of
  EVar ident -> failure x
  ELit literal -> failure x
  EParen exp -> failure x
  EArw exp ident -> failure x
  EFld exp ident -> failure x
  EArr exp1 exp2 -> failure x
  EApp exp exps -> failure x
  UOp uop exp -> failure x
  Mul exp1 exp2 -> failure x
  Div exp1 exp2 -> failure x
  Mod exp1 exp2 -> failure x
  Add exp1 exp2 -> failure x
  Sub exp1 exp2 -> failure x
  Lsl exp1 exp2 -> failure x
  Lsr exp1 exp2 -> failure x
  Lt exp1 exp2 -> failure x
  Gt exp1 exp2 -> failure x
  Le exp1 exp2 -> failure x
  Ge exp1 exp2 -> failure x
  Eq exp1 exp2 -> failure x
  NEq exp1 exp2 -> failure x
  And exp1 exp2 -> failure x
  Xor exp1 exp2 -> failure x
  Ior exp1 exp2 -> failure x
  Land exp1 exp2 -> failure x
  Lor exp1 exp2 -> failure x
  Cond exp1 exp2 exp3 -> failure x
transLVal :: LVal -> Result
transLVal x = case x of
  LVar ident -> failure x
  LArw lval ident -> failure x
  LFld lval ident -> failure x
  LArr lval exp -> failure x
  LPtr lval -> failure x

