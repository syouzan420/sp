import Haste (setTimer,Interval(Once,Repeat))
import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..)
                    ,MouseEvent(..),MouseData(..)
                    ,TouchEvent(..),TouchData(..),Touch(..))
import Haste.DOM (document,elemById,fromElem)
import Haste.Audio (play,Audio)
import Control.Monad.IO.Class (MonadIO,liftIO)
import Data.IORef(newIORef,readIORef,writeIORef)
import Loop (inputLoop,mouseClick,timerEvent)
import Browser (getCanvasInfo,cvRatio,tcStart,tcEnd,touchIsTrue,setBmps,setAudio)
import Define (State(..),Switch(..))
import Initialize (initState)

getCoords :: [Touch] -> [(Int,Int)]
getCoords = map (\(Touch _ _ _ cli _) -> cli)

addCoords :: [Touch] -> State -> State
addCoords tcs st = st{tccs=tccs st++[getCoords tcs]}

delCoords :: State -> State
delCoords st = st{tccs=[]}

showCoords :: MonadIO m => State -> m State
showCoords st = liftIO $ print (tccs st) >> return st

showTouch2 :: MonadIO m => [Touch] -> m ()
showTouch2 tcs = liftIO $ print (getCoords tcs)

showTouch :: MonadIO m => [Touch] -> m () 
showTouch [] = return ()
showTouch (Touch idn tar pag cli scr:xs) = do
  let s = "idintifier:" ++ show idn ++ " target:" ++ " " ++ 
          " pageCoords:" ++ show pag ++ " clientCoords:" ++ show cli ++ 
          " screenCoords:" ++ show scr
  liftIO $ putStrLn s  
  showTouch xs

playAudio :: Audio -> State -> IO State 
playAudio audio st = do
  let iAS = (ias . swc) st
  if iAS then return st else do
    play audio
    return st{swc=(swc st){ias=True}}

main :: IO ()
main = do
  bmps <- setBmps
  a <- setAudio
  Just ce <- elemById "canvas"
  Just c <- fromElem ce
  ci <- getCanvasInfo c
  state <- newIORef initState 
  onEvent document KeyDown $ \(KeyData kc _ _ _ _) -> do
    preventDefault
    readIORef state >>= inputLoop c ci bmps kc >>= writeIORef state
  onEvent ce Click $ \(MouseData xy _ _) -> do
    readIORef state >>= playAudio a >>= mouseClick c ci bmps xy >>= writeIORef state
  onEvent ce TouchStart $ \(TouchData a _ _) -> do
    showTouch2 a 
    readIORef state >>= tcStart >>= writeIORef state . delCoords
  onEvent ce TouchMove $ \ (TouchData a _ _) -> do
    showTouch2 a
    readIORef state >>= writeIORef state . addCoords a
  onEvent ce TouchEnd $ \(TouchData {}) -> do
    readIORef state >>= showCoords >>= touchIsTrue >>= writeIORef state
    setTimer (Once 100) $ readIORef state >>= tcEnd >>= writeIORef state
    return ()
  setTimer (Repeat 50) $
    readIORef state >>= timerEvent c ci bmps >>= writeIORef state
  return ()
