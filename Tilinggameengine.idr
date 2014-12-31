module Tilinggameengine

--------------------------------------------------------------------------------
-- Tiling Idris/JavaScript Game Engine
--------------------------------------------------------------------------------

data GridSize = mkGridSize Nat Nat

CellGrid : GridSize -> Type
CellGrid (mkGridSize m n) = Vect m (Vect n Int)

EncodeGrid : (size : GridSize) -> CellGrid size -> String
EncodeGrid (mkGridSize Z _) _ = ""
EncodeGrid (mkGridSize (S k) _) (r::rs) = (pack (map chr r)) ++ (EncodeGrid (mkGridSize k _) rs)

JSEvent : Type
JSEvent = Int

getNextEvent : (JSEvent -> IO ()) -> IO ()
getNextEvent cb = mkForeign (FFun "idris_interface.get_next_event(%0)" [FFunction FInt (FAny (IO ()))] FUnit) cb

initDisplay : Int -> Int -> IO ()
initDisplay m n = mkForeign (FFun "idris_interface.init_display(%0, %1)" [FInt, FInt] FUnit) m n

display : String -> IO ()
display str = mkForeign (FFun "idris_interface.show(%0)" [FString] FUnit) str

runEventLoop : (size : GridSize) -> a -> (a -> Int -> a) -> (a -> (CellGrid size)) -> IO ()
runEventLoop (mkGridSize m n) init trans view = do
  display (EncodeGrid (mkGridSize m n) (view init))
  getNextEvent (\x => runEventLoop (mkGridSize m n) (trans init x) trans view)

startEventLoop : (size : GridSize) -> a -> (a -> Int -> a) -> (a -> (CellGrid size)) -> IO ()
startEventLoop (mkGridSize m n) init trans view = do
  initDisplay (toIntNat m) (toIntNat n)
  runEventLoop (mkGridSize m n) init trans view