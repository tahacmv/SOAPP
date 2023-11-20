open util/ordering[Section]

// Signatures
abstract sig Section {
    door: one Door,
    cam: one Camera
}

sig LeftSection, CenterSection, RightSection extends Section {}

abstract sig DoorState {}

sig DoorOpen, DoorClosed extends DoorState {}

sig Door {
    state: one DoorState
}

abstract sig Camera {
    signal: one Signal,
    stopLocomotive: lone StopLocomotive
}

sig LeftCamera, RightCamera, CenterCamera extends Camera {}

abstract sig Signal {}

sig Presence, Absence extends Signal {}

abstract sig StopLocomotive {}

sig StopLocomotiveRight, StopLocomotiveLeft, StopLocomotiveCenter extends StopLocomotive {}

sig Train {
    left, center, right: lone Section
}

// Facts
fact sectionsDiffer {
    always (
        (some left) implies (Train.left != Train.center and Train.right != Train.left) and
        (some right) implies (Train.right != Train.center and Train.right != Train.left) and
        (some center) implies (Train.right != Train.center and Train.center != Train.left)
    )
}

fact uniqueDoors {
    all disj s1, s2: Section | s1.door != s2.door
}

fact uniqueCameras {
    all disj s1, s2: Section | s1.cam != s2.cam
}

fact oneSectionEachType {
    always lone LeftSection and lone CenterSection and lone RightSection
}

fact cameraSectionMapping {
    always (
        (LeftSection.cam = LeftCamera) and
        (CenterSection.cam = CenterCamera) and
        (RightSection.cam = RightCamera)
    )
}

fact initialConditions {
    always (
        (some StopLocomotiveLeft) and (StopLocomotiveLeft in StopLocomotive) and
        (some StopLocomotiveRight) and (StopLocomotiveRight in StopLocomotive) and
        (some StopLocomotiveCenter) and (StopLocomotiveCenter in StopLocomotive) and
        (some DoorOpen) and (some DoorClosed)
    )
}

fact initialDoorAndSignalStates {
    all s: Section | s.door.state = DoorClosed
}

fact initialCameraSignals {
    all c: Camera | c.signal = Absence
}

fact noTrainsInitially {
    no Train.left
    no Train.center
    no Train.right
    no RightCamera.stopLocomotive
    no LeftCamera.stopLocomotive
    no CenterCamera.stopLocomotive
}

// Train detection happens after all cameras send a Presence signal
fact trainDetection {
    all c: Camera |
        always (
            (some c.stopLocomotive) implies (some Presence and Presence in c.signal)
        )
}

fact atLeastOneTrain {
    always one Train
}

// Two sections with the same door and camera are identical
fact identicalSections {
    all s1, s2: Section |
        (s1.cam = s2.cam and s1.door = s2.door) implies s1 = s2
}

// System behavior
fact systemBehavior {
    always (
        skip or (
            some t: Train, s: Section |
                advanceTrainLeftSection[t, s] or
                advanceTrainCenterSection[t, s] or
                advanceTrainRightSection[t, s] or
                stopLocomotivePred or
                openDoors
        )
    )
}

// Predicates
pred trainDetected[cam: Camera] {
    Absence in cam.signal
    cam.signal' = Presence
    right' = right
    left' = left
    center' = center
    state' = state
    stopLocomotive' = stopLocomotive
}

pred advanceTrainLeftSection[t: Train, s: Section] {
    no t.left
    no t.center
    no t.right
    LeftSection in s
    RightCamera.signal' = Presence
    t.right' = LeftSection
    left' = left
    center' = center
    Door.state' = DoorClosed
    stopLocomotive' = stopLocomotive
    all s2: Section - s | s2.cam.signal' = s2.cam.signal
}

pred advanceTrainCenterSection[t: Train, s: Section] {
    no t.left
    no t.center
    CenterSection in s
    some right
    t.right' = CenterSection
    t.center' = LeftSection
    CenterCamera.signal' = Presence
    left' = left
    Door.state' = DoorClosed
    stopLocomotive' = stopLocomotive
    all s2: Section - s | s2.cam.signal' = s2.cam.signal
}

pred advanceTrainRightSection[t: Train, s: Section] {
    no t.left
    RightSection in s
    some right
    some center
    t.right' = RightSection
    t.center' = CenterSection
    t.left' = LeftSection
    RightCamera.signal' = Presence
    Door.state' = DoorClosed
    stopLocomotive' = stopLocomotive
    all s2: Section - s | s2.cam.signal' = s2.cam.signal
}

pred stopLocomotivePred {
    Presence in RightCamera.signal
    Presence in LeftCamera.signal
    Presence in CenterCamera.signal
    LeftCamera.stopLocomotive' = StopLocomotiveLeft
    RightCamera.stopLocomotive' = StopLocomotiveRight
    CenterCamera.stopLocomotive' = StopLocomotiveCenter
    signal' = signal
    right' = right
    left' = left
    center' = center
    Door.state' = DoorClosed
}

pred openDoors {
    StopLocomotiveLeft in LeftCamera.stopLocomotive
    StopLocomotiveRight in RightCamera.stopLocomotive
    StopLocomotiveCenter in CenterCamera.stopLocomotive
    Door.state' = DoorOpen
    signal' = signal
    right' = right
    left' = left
    center' = center
    stopLocomotive' = stopLocomotive
}

pred trainDetected[cam: Camera] {
    Absence in cam.signal
    cam.signal' = Presence
    all cam: Camera - cam | cam.signal' = cam.signal
}

pred trainIdentified[cam: Camera] {
    all cam: Camera | cam.signal = Presence
    state' = state
    signal' = signal
    left' = left
    center' = center
    right' = right
}

pred arretTrain {
    all c: Camera | (some c.stopLocomotive)
}

pred skip {
    state' = state
    signal' = signal
    left' = left
    center' = center
    right' = right
    stopLocomotive' = stopLocomotive
}

// Assertions
assert Safety {
    all p: Door {
        always (((some DoorOpen) and (DoorOpen in p.state)) implies before (arretTrain))
    }
}

assert Liveness {
    always (
        (arretTrain) implies (after (all p: Door | (some DoorOpen) and (DoorOpen in p.state)))
    )
}

// Checks
check Safety
check Liveness

// Run command
run {} for 1 Train, 3 Section, 3 Door, 3 DoorState, 3 Camera, exactly 2 Signal, exactly 3 StopLocomotive
