---------------- Signatures ----------------

abstract sig Person {}

sig Faculty extends Person {
  incommittee: one Graduate 
}

abstract sig Student extends Person {
  id: one Id,
  transcript: set Course,
  major: one Department
}

sig Undergrad extends Student {}

sig Graduate extends Student {
  advisor: one Faculty 
}

sig Instructor in Person {
  department: one Department
}

sig Course {
  taughtby: one Instructor,
  enrolled: some Student,
  waitlist: set Student, 
  prerequisites: set Course
}

sig Id {}

sig Department { 
  courses: some Course, 
  required: some Course 
} 

---------------- Fact ----------------

fact  {
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
  all s1,s2: Student | s1 != s2 => s1.id != s2.id

  -- There are no cycles in the prerequisite dependences 
  all c: Course | c !in c.^prerequisites

  -- A student can only have, wait for or take a course for which they have the prerequisites
   all s: Student | (waitlist.s + enrolled.s + s.transcript).prerequisites in s.transcript



  -- Each department has at least one instructor
  all d: Department | some department.d

  -- Each course is in a single department
  all c: Course | one c.~courses and one c.~required



  -- Advisors are always on their student's committees
  all g: Graduate | some incommittee.g => g.advisor in incommittee.g

  -- Students are advised by faculty in their major
  all g: Graduate | g.advisor in department.(g.major)

   -- Required courses for a major are courses in that major
  all d: Department | d.required in d.courses

 -- Only faculty teach required courses
  all d: Department | d.required.taughtby in Faculty

  -- Faculty members only teach courses in their department
  all f: Faculty | courses.(taughtby.f) = f.department

  -- Students must be enrolled in at least one course from their major
  all s: Student | some (enrolled.s & s.major.courses)
}

------------------- Run ---------------------

pred RealismConstraints [] {
  -- There is a graduate student who is an instructor
  some Graduate & Instructor 

  -- There are at least two courses
  #Course >= 2

  -- There are at least three undergraduates
  #Undergrad > 2

  -- There exists a course with prerequisites that someone is enrolled in
  some c: Course | some c.prerequisites and some c.enrolled

  -- There are at least two departments and some required courses.
  #Department > 1
  some Department.required
} 

run RealismConstraints

---------------- Assertion ----------------

-- No instructor is on the waitlist for a course that he/she teaches
assert NoWaitingTeacher {
  all c: Course | no (c.taughtby & c.waitlist)
}
// check NoWaitingTeacher for 10

-- A student's committee members are faculty in his/her major.
assert CommitteeMembersInMajor {
  all s: Student | (incommittee.s).department in s.major
} 
// check CommitteeMembersInMajor
