---------------- Signatures ----------------

abstract sig Person {}

sig Faculty extends Person {}

abstract sig Student extends Person {}

sig Graduate, Undergrad extends Student {}

sig Instructor in Person {}

sig Course {
  taughtby: one Instructor,
  enrolled: some Student,
  waitlist: set Student
}

fun teaches : Instructor -> Course { ~taughtby }

---------------- Fact ----------------

fact 
{
  -- All instructors are either Faculty or Graduate Students

  -- No one is waiting for a course unless someone is enrolled

  -- Graduate students do not teach courses they are enrolled in
  -- or wainting to enroll in

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

-- run RealismConstraints for 4 

---------------- Assertions ----------------

-- Note: to check the assertion below you must comment the run command
-- above first (similarly for the second check)

-- No instructor is on the waitlist for a course that he/she teaches
assert NoWaitingTeacher {

}
-- check NoWaitingTeacher for 10

-- No student is enrolled and on the waitlist for the same course
assert NoEnrolledAndWaiting {

}

check NoEnrolledAndWaiting for 10












