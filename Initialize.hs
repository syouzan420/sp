module Initialize where

import Define(State(..),Play(..),Switch(..),Dir(..))
import Messages(initMsg)
import Stages(stages,players,initPos,gridSize,idef,evts)
import Grid(makeGrid)

initState :: State
initState = State {player=initPlayer, sz=igs, msg=initMsg, ems=[]
                  ,evt=evts, ecs=replicate (length evts) 0, mem=[]
                  ,mps=(0,0), mct=0, mcl=0, msc=0, jps= -1
                  ,chd=[], chn=0, rek=[], rdt=[], rtc=0, rtl=[], chr=(4,0), tic=0
                  ,swc=initSwitch, db=""}
                     where igs = head gridSize

initPlayer :: Play
initPlayer = Play {xy=head initPos, gr=makeGrid igs (head stages), dr = Dw
                  ,pl=head players, et=' ', sn=0, edf=[]
                  ,rgn=0, elg="", iw=False,isc=False}
                     where igs = head gridSize

initSwitch :: Switch
initSwitch = Switch {ils=False,igc=False,ims=True,imp=False,itc=False
                    ,ini=False,ich=False,ism=False,ias=False}

