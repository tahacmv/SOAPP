// Project SOAPP
// Authors : Taha Mouatassim
//        : Ayoub Kasi

abstract one sig Quay{
    train: one Train
}

// A train is composed of 2 locomotives and central wagons
one sig Train {
    leftLoco: one LeftLocomotive,
    centralWagons: one CentralWagon,
    rightLoco: one RightLocomotive
}

// A wagon can be of 3 different types and has one or more neighboring wagons
abstract sig Wagon {
}
one sig CentralWagon extends Wagon{
    leftNeighbor: one Wagon,
    rightNeighbor: one Wagon
}

one sig RightLocomotive extends Wagon {
    leftNeighbor: one Wagon
}
one sig LeftLocomotive extends Wagon {
    rightNeighbor: one Wagon
}


// A section belongs to a quay, can be of 3 types, and may or may not contain a wagon
abstract sig Section{
    belongsTo: one Quay,
    wagon: lone Wagon
}
one sig SectionCentral extends Section{
    door: one Door
}
one sig SectionRight extends Section{
    door: one Door
}
one sig SectionLeft extends Section{
    door: one Door
}


// Each door can be either open or closed
abstract sig Door{
    state: one State
}
one sig DoorCentral extends Door{
    section: one Section,
    wagon: one CentralWagon
}
one sig DoorRight extends Door{
    section: one Section,
    wagon: one RightLocomotive
}
one sig DoorLeft extends Door{
    section: one Section,
    wagon: one LeftLocomotive
}
abstract sig State {}
sig Open, Close extends State{}


// We assign a camera to each section
sig Camera{
    detected: lone Wagon
}

one sig CamLeft extends Camera{
    positionOn: one SectionLeft,
}
one sig CamCentral extends Camera{
    positionOn: one SectionCentral,
}
one sig CamRight extends Camera{
    positionOn: one SectionRight,
}
// If the central camera detects a wagon, one of the other cameras should detect a wagon
fact trainDetection{
    always{ 
        some CamCentral.detected implies some CamRight.detected or some CamLeft.detected
         ((CamCentral.detected in LeftLocomotive) or 
        (CamCentral.detected in RightLocomotive)) 
        implies ((CamLeft.detected in CentralWagon) or (CamRight.detected in CentralWagon))
    }
}

// Initial state: doors are open, and the train is properly positioned
fact init {
    no Close
    CamLeft.detected = LeftLocomotive
    CamRight.detected = RightLocomotive
    CamCentral.detected = CentralWagon
    SectionLeft.wagon = CamLeft.detected
    SectionRight.wagon = CamRight.detected
    SectionCentral.wagon = CamCentral.detected
}

// Open or close - these are the possible states of the doors
fact stateManagement{
    all state: State { 
        (state in Open) or (state in Close)
    }
}

// Avoid impossible situations
fact neighborhood{
    some w: LeftLocomotive | w.rightNeighbor in CentralWagon // The left locomotive is necessarily connected to a central wagon 
    some w: RightLocomotive | w.leftNeighbor in CentralWagon
    all lg: LeftLocomotive,w:CentralWagon | (lg.rightNeighbor=w) implies (w.leftNeighbor=lg)
    all ld: RightLocomotive,w:CentralWagon | (ld.leftNeighbor=w) implies (w.rightNeighbor=ld)

    all w: CentralWagon | w.leftNeighbor != w.rightNeighbor // A left neighbor is necessarily different from a right neighbor

    all w1,w2: CentralWagon | (w1 = w2.rightNeighbor) implies (w2 = w1.leftNeighbor) // The neighborhood relation is reciprocal
    all w1,w2: CentralWagon | (w1 in w2.leftNeighbor) implies (w2 in w1.rightNeighbor)

    all lg: LeftLocomotive | lg.rightNeighbor in CentralWagon  // The right neighbor of lg (resp. ld) is CentralWagon
    all ld: RightLocomotive | ld.leftNeighbor in CentralWagon
    
    all w: CentralWagon | w.leftNeighbor != w and w.rightNeighbor != w // A wagon cannot be its own neighbor
    all w: RightLocomotive | w.leftNeighbor != w
    all w: LeftLocomotive | w.rightNeighbor != w


    all s: SectionCentral | s.door in DoorCentral  // Each section in connection with its corresponding door
    all s: SectionRight | s.door in DoorRight
    all s: SectionLeft | s.door in DoorLeft

    all p: DoorCentral | p.section in SectionCentral  // Each door in connection with its corresponding section
    all p: DoorRight | p.section in SectionRight
    all p: DoorLeft | p.section in SectionLeft

}

// A section is occupied by a train
pred occupiedBy[t:Train, s: Section] {
    (s.wagon = t.leftLoco) or (s.wagon = t.rightLoco) or (s.wagon = t.centralWagons)
}

// The train advances
pred trainAdvances[t:Train] {
    some s: Section {
        s.wagon' != s.wagon
    }
}

// The train does not advance
pred trainImmobile[t:Train] {
    all s: Section {
        s.wagon' = s.wagon
    }
}

// SKIP
pred skip{
    State' = State
    Camera' = Camera
    Section' = Section    
}

// Open Door
pred openDoor[p: Door]{
    p.state in Open
}
// Close Door
pred closeDoor[p: Door]{
    p.state in Close
}


pred openDoorSection[camCentral: CamCentral, camLeft: CamLeft, camRight: CamRight, door: Door, train: Train]{
        ((camCentral.detected in CentralWagon) and 
        (camLeft.detected in LeftLocomotive) and 
        (camRight.detected in RightLocomotive)) and 
        (trainImmobile[train]) implies openDoor[door]
}

pred closeDoorSection[camCentral: CamCentral, camLeft: CamLeft, camRight: CamRight, door: Door, train: Train]{
        ((camCentral.detected not in CentralWagon) or 
        (camLeft.detected not in LeftLocomotive) or
        (camRight.detected not in RightLocomotive)) or 
        (not trainImmobile[train]) implies closeDoor[door]
}

fact behavior{
    always (
        skip or 
        (some t: Train | trainAdvances[t] or trainImmobile[t]) or
        (some t: Train, cc, cl, cr: Camera, disj d: Door | openDoorSection[cc, cl, cr, d, t]) or
        (some t: Train, cc, cl, cr: Camera, disj d: Door | closeDoorSection[cc, cl, cr, d, t])
    )
}

assert safety{
    always lone Train   

    always one CamCentral 
    always one CamLeft
    always one CamRight

    always CamCentral.positionOn = SectionCentral 
    always CamLeft.positionOn = SectionLeft
    always CamRight.positionOn = SectionRight
}

assert liveness {
    eventually Door.state' != Door.state 
    eventually some Camera.detected 
}

run{}   
