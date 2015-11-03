module myTaxiService

//PROBLEMI:
// - se impongo dei vincoli sui valori della data (ora commentati) dice che il modello è inconsistente (anche senza nessun fact)

//FACTS da fare:
// - se ad un driver è associata un richiesta non ancora finita, il driver deve star guidando un taxi
//....

//Primitive types

abstract sig Boolean {}
one sig TRUE extends Boolean {}
one sig FALSE extends Boolean {}

sig Strings {}

sig Coordinate {
	isInside: lone CityZone
}

sig Date {
	day: Int,
	month: Int,
	year: Int,

	hour: Int,
	min: Int
}

//Sigratures

abstract sig Account {
	username: Strings,
	password: Strings,
	email: Strings,
	validated: Boolean,

	receives: set Notification
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
	acceptedRequests: Int,
	refusedRequests: Int,

	takesCareOf: set Request,
	currentlyDriving: lone Taxi
}{
		acceptedRequests >= 0
		refusedRequests >= 0 
		validated = TRUE
	}

abstract sig Notification {
	msg: Strings,

	refersTo: Request,
	receiver: Account
}

sig InformativeNotification extends Notification {}

sig AcceptRefuseNotification extends Notification {
	accepted: Boolean,
	responseTimeLimit: Int
}

abstract sig Request {
	startingLocation: Coordinate,
	appointmentTime: Date,
	completed: Boolean,
	missingClient: Boolean,

	sender: PassengerAccount,
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
	passengerCapacity: Int,

	currentlyIn: lone CityZone,
	driver: lone DriverAccount
}{
		passengerCapacity > 0
}

//Facts

fact InverseRelations {
	sends = ~sender and
	receives = ~receiver and
	isAssociatedTo = ~takesCareOf and
	driver = ~currentlyDriving
}

//A passenger account that is not yet validated, cannot take part of any relations
fact NotValidatedAccountCannotDoNothing{
	no psgr: PassengerAccount | psgr.validated = FALSE and (#psgr.sends > 0 or #psgr.inWaitingQueue > 0 or #psgr.hasReservationHistory > 0)
}

//Usernames and mails are unique
fact UniqueUsernameEmail{
	no disj a1, a2 : Account | a1.username = a2.username || a1.email = a2.email
}

//Taxis' ID are unique
fact UniqueTaxiID{
	no disj t1, t2: Taxi | t1.taxiCode = t2.taxiCode
}

//If a taxi is in a certain CityZone, its position must be inside that CityZone
fact TaxiPosition{
	all t: Taxi, z: CityZone | t.currentlyIn = z <=> t.currentPosition.isInside = z
}

//Reservations that are inside the history of a PassengerAccount, must have that user as sender
fact ReservationHistoryConsistency{
	all p: PassengerAccount, r: Reservation | r in p.hasReservationHistory => r.sender = p
}

//If a driver is inside the queue of a certain CityZone, he has to be available and has to drive a taxi that is inside the same CityZone
fact DriverQueueZone {
	all d: DriverAccount, z: CityZone | d in z.driverQueue => ( #d.currentlyDriving = 1 and d.currentlyDriving.currentlyIn = z and d.available = TRUE )
}

//If a passenger is inside the queue of a certain zone, there must be a request, which starting location is inside that CityZone, sent by the user that is not yet completed and associated to any driver
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
	no d: DriverAccount, disj r1, r2: Request | r1 in d.takesCareOf and r2 in d.takesCareOf and r1.completed = FALSE and r2.completed = FALSE
}

//All the requests that are completed are associated to a driver
fact CompletedRequestDriver{
	all r: Request | r.completed = TRUE => #r.isAssociatedTo = 1
}

//There cannot be two or more requests associated to a driver at the same appointmentTime
fact DuplicatedRequestDriver{
	no d: DriverAccount, disj r1, r2: Request | r1.isAssociatedTo = d and r2.isAssociatedTo = d and
	r1.appointmentTime.year = r2.appointmentTime.year and
	r1.appointmentTime.month = r2.appointmentTime.month and
	r1.appointmentTime.day = r2.appointmentTime.day and
	r1.appointmentTime.hour = r2.appointmentTime.hour and
	r1.appointmentTime.min = r2.appointmentTime.min
}

//Per ogni richiesta associata ad un driver deve esistere una notifica riguardante quella richiesta e inviata al driver che è stata accettata
fact NotificationForEachDriverRequest{
	all r: Request, d: DriverAccount | r.isAssociatedTo = d => (one n: AcceptRefuseNotification | n.accepted = TRUE and n.receiver = r.isAssociatedTo and n.refersTo = r)
}

//For each reservation there cannot be a notification that refers to it refused by a driver 
fact NoRefusedNotificationForAssignedReservation{
	all r: Reservation | ( no n: AcceptRefuseNotification | n.refersTo = r and n.accepted = FALSE )
}

//Functions
fun requestedRide[p: PassengerAccount] :
	set Ride { p.sends & Ride }

fun incompleteRequestedRide[p: PassengerAccount] :
	set Ride { requestedRide[p]  & {r: Ride | r.completed = FALSE} }

//Predicates

//run showDuplicatedRequestDriver for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 1 Taxi, 1 CityZone, 2 Coordinate, 2 Request, 2 Date
pred showDuplicatedRequestDriver [d: DriverAccount, r1: Request, r2: Request]{
	r1 != r2 and r1.isAssociatedTo = d and r2.isAssociatedTo = d
	r1.appointmentTime.year = r2.appointmentTime.year and
	r1.appointmentTime.month = r2.appointmentTime.month and
	r1.appointmentTime.day = r2.appointmentTime.day and
	r1.appointmentTime.hour = r2.appointmentTime.hour
}

//run showNotificationForEachDriverRequest for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 1 Taxi, 1 CityZone, 2 Coordinate, 2 Request, 2 Date, 1 Notification, 2 Strings
pred showNotificationForEachDriverRequest [d: DriverAccount, r: Request]{
	r.isAssociatedTo = d
}

//run showNoRefusedNotificationForAssignedReservation for 5 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 1 Taxi, 1 CityZone, 2 Coordinate, 1 Reservation, 1 Request, 2 Date, 1 Notification, 2 Strings
pred showNoRefusedNotificationForAssignedReservation [d: DriverAccount, r: Reservation]{
	r in d.takesCareOf
}

//run showTaxiQueueZone for 10 but 1 DriverAccount, 1 Account, 0 Notification, 1 Taxi, 1 CityZone, 3 Coordinate
pred showTaxiQueueZone [ d: DriverAccount, t: Taxi, z: CityZone ] {
	t.currentlyIn = z and d.currentlyDriving = t and d in z.driverQueue
}

//run showPassengerQueueZone for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 1 Ride, 1 Date, 3 Coordinate
pred showPassengerQueueZone [p: PassengerAccount, z: CityZone] {
	p in z.passengerQueue
}
