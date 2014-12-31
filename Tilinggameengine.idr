module Tilinggameengine

--------------------------------------------------------------------------------
-- Tiling Idris/JavaScript Game Engine
--------------------------------------------------------------------------------

getNextEvent : (Int -> IO ()) -> IO ()
getNextEvent cb = mkForeign (FFun "idris_interface.get_next_event(%0)" [FFunction FInt (FAny (IO ()))] FUnit) cb

initDisplay : Int -> Int -> IO ()
initDisplay m n = mkForeign (FFun "idris_interface.init_display(%0, %1)" [FInt, FInt] FUnit) m n

display : String -> IO ()
display str = mkForeign (FFun "idris_interface.show(%0)" [FString] FUnit) str

--------------------------------------------------------------------------------
-- Keyboard input
--------------------------------------------------------------------------------

data KeyboardInput = LeftArrow | UpArrow | RightArrow | DownArrow
                     | Character Char | UnknownKey

decodeInput : Int -> KeyboardInput
decodeInput 37 = LeftArrow
decodeInput 38 = UpArrow
decodeInput 39 = RightArrow
decodeInput 40 = DownArrow
decodeInput n  = if (48 <= n && n < 91) then Character (chr n) else UnknownKey

--------------------------------------------------------------------------------
-- Display output
--------------------------------------------------------------------------------

data GridSize = mkGridSize Nat Nat

CellGrid : GridSize -> Type
CellGrid (mkGridSize m n) = Vect m (Vect n Int)

encodeOutput : (size : GridSize) -> CellGrid size -> String
encodeOutput (mkGridSize Z _) _ = ""
encodeOutput (mkGridSize (S k) _) (r::rs) = (pack (map chr r)) ++ (encodeOutput (mkGridSize k _) rs)

--------------------------------------------------------------------------------
-- Main event loop
--------------------------------------------------------------------------------

runEventLoop : (size : GridSize) -> a -> (a -> KeyboardInput -> a) -> (a -> (CellGrid size)) -> IO ()
runEventLoop (mkGridSize m n) init trans view = do
  display (encodeOutput (mkGridSize m n) (view init))
  getNextEvent (\x => runEventLoop (mkGridSize m n) (trans init (decodeInput x)) trans view)

startEventLoop : (size : GridSize) -> a -> (a -> KeyboardInput -> a) -> (a -> (CellGrid size)) -> IO ()
startEventLoop (mkGridSize m n) init trans view = do
  initDisplay (toIntNat m) (toIntNat n)
  runEventLoop (mkGridSize m n) init trans view