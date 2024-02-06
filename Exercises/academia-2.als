---------------- Signatures ----------------

abstract sig Person {}

sig Faculty extends Person {}

abstract sig Student extends Person {
  id: one Id,
  transcript: set Course
}

sig Graduate, Undergrad extends Student {}

sig Instructor in Person {}

sig Course {
  taughtby: one Instructor,
  enrolled: some Student,
  waitlist: set Student, 
  prerequisites: set Course
}

sig Id {}

---------------- Fact ----------------

fact 
{
  -- All instructors are either Faculty or Graduate Students
  all i: Instructor | i in Faculty+Graduate 

  -- No one is waiting for a course unless someone is enrolled
  all c: Course | some c.waitlist => some c.enrolled

  -- Graduate students do not teach courses they are enrolled in
  -- or wainting to enroll in
  all c: Course | c.taughtby !in c.enrolled + c.waitlist

  -- No student is enrolled and on the waitlist for the same course
  all c: Course | no (c.enrolled & c.waitlist)



  -- No two distinct students have the same ID
  all s1, s2: Student | s1 != s2 => s1.id != s2.id

  -- A student can only have a course for which they have the prerequisites
  all s: Student | s.transcript.prerequisites in s.transcript

  -- There are no cycles in the prerequisite dependencies 
  all c: Course | c !in c.^prerequisites
}

------------------- Run ---------------------

pred RealismConstraints [] {
  -- There is a graduate student who is an instructor
  some Graduate & Instructor 

  -- There are at least two courses
  #Course >= 2

  -- There are at least three undergraduates
  #Undergrad > 2

} 

run RealismConstraints for 4



---------------- Assertion ----------------

-- No instructor is on the waitlist for a course that he/she teaches
assert NoWaitingTeacher {
  all c: Course | no (c.taughtby & c.waitlist)
}
check NoWaitingTeacher for 10


-- A student can only wait to be in a course for which they have the prerequisites
assert AllWaitsHavePrereqs {
     all s: Student | (waitlist.s).prerequisites in s.transcript
}
check AllWaitsHavePrereqs











