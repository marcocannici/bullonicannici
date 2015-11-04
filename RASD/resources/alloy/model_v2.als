module myTaxiService

//Primitive types

abstract sig Boolean {}
one sig TRUE extends Boolean {}
one sig FALSE extends Boolean {}

sig Strings {}

sig Coordinate {
	isInside: lone CityZone
}

sig Date {}

//Sigratures

abstract sig Account {
	username: Strings,
	email: Strings,
	validated: Boolean,
	//password: Strings

}

sig AdministratorAccount extends Account {}
{
	validated = TRUE
}

sig PassengerAccount extends Account {
	sends: set Request,
	hasReservationHistory: set Reservation,
	inWaitingQueue: lone CityZone
}

sig DriverAccount extends Account {
	available: Boolean,
	//acceptedRequests: Int,
	//refusedRequests: Int,

	//takesCareOf: set Request,
	currentlyDriving: lone Taxi
}{
		validated = TRUE
	}

abstract sig Notification {
	//msg: Strings

	refersTo: Request,
	receiver: Account
}

sig InformativeNotification extends Notification {}

sig AcceptRefuseNotification extends Notification {
	accepted: Boolean,
//	responseTimeLimit: Int
}

abstract sig Request {
	startingLocation: Coordinate,
	appointmentTime: Date,
	completed: Boolean,
	missingClient: Boolean,

	isAssociatedTo: lone DriverAccount
}

sig Ride extends Request {}

sig Reservation extends Request {
	endingLocation: Coordinate
}{
		startingLocation != endingLocation
	}

sig CityZone {
	edges: some Coordinate,
	passengerQueue: set PassengerAccount,
	driverQueue: set DriverAccount
}{
		#edges >= 3
}

sig Taxi {
	taxiCode: Strings,
	currentPosition: Coordinate,
//	passengerCapacity: Int,

	currentlyIn: lone CityZone,
}

//Facts

fact RelationsCardinality{
	all r: Request | #r.~sends = 1
	all t: Taxi | #t.~currentlyDriving <= 1
}

//A passenger account that is not yet validated cannot take part of any relations
fact NotValidatedAccountCannotDoNothing{
	no psgr: PassengerAccount | psgr.validated = FALSE and (#psgr.sends > 0 or #psgr.inWaitingQueue > 0 or #psgr.hasReservationHistory > 0)
}

//Usernames, mails and Taxi ID are unique
fact UniqueUsernameEmail{
	no disj a1, a2 : Account | a1.username = a2.username || a1.email = a2.email
	no disj t1, t2: Taxi | t1.taxiCode = t2.taxiCode
}

//If a taxi is in a certain CityZone, its position must be inside that CityZone
fact TaxiPosition{
	all t: Taxi, z: CityZone | t.currentlyIn = z <=> t.currentPosition.isInside = z
}

//Reservations that are inside the history of a PassengerAccount, must have the same user as sender
fact ReservationHistoryConsistency{
	all p: PassengerAccount, r: Reservation | r in p.hasReservationHistory => r.(~sends) = p
}

//If a driver is availabe he must be driving a taxi
fact DriverAvailableIsDriving{
	all d: DriverAccount | d.available = TRUE => #d.currentlyDriving = 1
}

//If a driver is inside the queue of a certain CityZone, he has to be available and must be driving a taxi that is inside the same CityZone
fact DriverQueueZone {
	all d: DriverAccount, z: CityZone | d in z.driverQueue => ( #d.currentlyDriving = 1 and d.currentlyDriving.currentlyIn = z and d.available = TRUE )
}

//If a passenger is inside the queue of a certain zone, there must be a request, whose starting location is inside that CityZone, that is not yet completed and not associated to any driver
fact PassengerQueueZone{
	all p: PassengerAccount, z: CityZone | p in z.passengerQueue <=> ( #incompleteRequestedRide[p] = 1 && #incompleteRequestedRide[p].isAssociatedTo = 0 && incompleteRequestedRide[p].startingLocation.isInside = z)
}

//For each passenger user, there can be only one ride request not yet completed
fact PassengerIncompletedRide{
	all p: PassengerAccount | #incompleteRequestedRide[p] <= 1
}

//If a request is not yet completed then the missingClient field must be false
fact MissingClientIncompletedRequest{
	all r : Request | r.completed = FALSE => r.missingClient = FALSE
	all r : Request | r.missingClient = TRUE => r.completed = TRUE
}

//For each driver, there can be only one request associated to him that is not yet completed
fact IncompleteDriverRequests{
	no d: DriverAccount, disj r1, r2: Request | r1 in d.(~isAssociatedTo) and r2 in d.(~isAssociatedTo) and r1.completed = FALSE and r2.completed = FALSE
}

//All the requests that are completed are associated to a driver
fact CompletedRequestDriver{
	all r: Request | r.completed = TRUE => #r.isAssociatedTo = 1
}

//There cannot be two or more requests associated to a driver at the same appointmentTime
fact DuplicatedRequestDriver{
	no d: DriverAccount, disj r1, r2: Request | r1.isAssociatedTo = d and r2.isAssociatedTo = d and
	r1.appointmentTime = r2.appointmentTime
}

//There cannot be two or more requests sent by a passenger at the same appointmentTime
fact DuplicatedRequestDriver{
	no p: PassengerAccount, disj r1, r2: Request | r1 in p.sends and r2 in p.sends and
	r1.appointmentTime = r2.appointmentTime
}

//For each request associated to a driver there must be a notification sent to the same driver that has been accepted
fact NotificationForEachDriverRequest{
	all r: Request, d: DriverAccount | r.isAssociatedTo = d => (one n: AcceptRefuseNotification | n.accepted = TRUE and n.receiver = r.isAssociatedTo and n.refersTo = r)
}

//For each reservation there cannot be a refused notification that refers to it 
fact NoRefusedNotificationForAssignedReservation{
	all r: Reservation | ( no n: AcceptRefuseNotification | n.refersTo = r and n.accepted = FALSE )
}

//Functions
fun requestedRide[p: PassengerAccount] :
	set Ride { p.sends & Ride }

fun incompleteRequestedRide[p: PassengerAccount] :
	set Ride { requestedRide[p]  & {r: Ride | r.completed = FALSE} }

//Predicates

run show for 10 but 2 Notification, 2 Request, 0 Taxi, 1 CityZone, 2 Coordinate
pred show{
	some d: DriverAccount, p:PassengerAccount, r: Request, n: AcceptRefuseNotification |
	 r.isAssociatedTo != d and r in p.sends and r.completed = TRUE and n.accepted = FALSE and n.refersTo = r and n.receiver = d
}

//run showDriverNotification for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 1 Taxi, 1 CityZone, 1 Coordinate, 1 Request, 1 Date, 1 Notification, 2 Strings
pred showDriverNotification [d: DriverAccount, r: Request]{
	r.isAssociatedTo = d
}

//run showTaxiQueueZone for 10 but 1 DriverAccount, 1 Account, 0 Notification, 1 Strings, 3 Coordinate, 0 Date
pred showTaxiQueueZone [ d: DriverAccount, t: Taxi, z: CityZone ] {
	t.currentlyIn = z and d.currentlyDriving = t and d in z.driverQueue and #CityZone = 1 and #Taxi = 1
}

//run showPassengerQueueZone for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 1 Ride, 1 Date, 3 Coordinate
pred showPassengerQueueZone [p: PassengerAccount, z: CityZone] {
	p in z.passengerQueue
}
