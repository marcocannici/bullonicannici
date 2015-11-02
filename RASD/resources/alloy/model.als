module myTaxiService

//PROBLEMI:
// - se impongo dei vincoli sui valori della data (ora commentati) dice che il modello è inconsistente (anche senza nessun fact)

//FACTS da fare:
// - il contatore accepted/refused dei driver deve corrispondere al numero di notification accettate/rifiutate associate ad una Request associata al driver ?
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
	year: Int
}{
/*	day >= 1 and day <= 31 and
	month >= 1 and month <= 12*/
}

//Sigratures

abstract sig Account {
	username: Strings,
	password: Strings,
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

//Un account non ancora validato non deve rientrare in nessuna relazione di PassengerAccount
fact NotValidatedAccountCannotDoNothing{
	no psgr: PassengerAccount | psgr.validated = FALSE and (#psgr.sends > 0 or #psgr.inWaitingQueue > 0 or #psgr.hasReservationHistory > 0)
}

//Gli username sono unici
fact UniqueUsernames{
	no disj a1, a2 : Account | a1.username = a2.username
}

//Gli ID dei taxi sono unici
fact UniqueTaxiID{
	no disj t1, t2: Taxi | t1.taxiCode = t2.taxiCode
}

//Se un taxi è in una zona, la sua posizione deve appartenere alla zona
fact TaxiPosition{
	all t: Taxi, z: CityZone | t.currentlyIn = z <=> t.currentPosition.isInside = z
}

//Le reservation in storia devono avere come sender l'account stesso
fact ReservationHistoryConsistency{
	all p: PassengerAccount, r: Reservation | r in p.hasReservationHistory => r.sender = p
}

//Se un driver è in coda in una zona allora deve star guidando un taxi che si trova in quella zona e deve essere disponibile
fact DriverQueueZone {
	all d: DriverAccount, z: CityZone | d in z.driverQueue => ( #d.currentlyDriving = 1 and d.currentlyDriving.currentlyIn = z and d.available = TRUE )
}

//Se un passeggero è in coda in una zona allora deve esistere una richiesta inviata da lui non ancora completa e a cui non è ancora stato assegnato un driver
fact PassengerQueueZone{
	all p: PassengerAccount, z: CityZone | p in z.passengerQueue <=> ( #incompleteRequestedRide[p] = 1 && #incompleteRequestedRide[p].isAssociatedTo = 0 && incompleteRequestedRide[p].startingLocation.isInside = z)
}

//Può esistere una sola richiesta ride non completata associata ad uno stesso utente
fact PassengerIncompletedRide{
	all p: PassengerAccount | #incompleteRequestedRide[p] <= 1
}

//Se una richiesta è incompleta, missingClient = FALSE
fact MissingClientIncompletedRequest{
	all r : Request | r.completed = FALSE => r.missingClient = FALSE
}

//Può esistere una sola richiesta non completata associata ad un driver
fact IncompleteDriverRequests{
	no d: DriverAccount, disj r1, r2: Request | r1 in d.takesCareOf and r2 in d.takesCareOf and r1.completed = FALSE and r2.completed = FALSE
}

//Tutte le richieste completate devono essere associate ad un driver
fact CompletedRequestDriver{
	all r: Request | r.completed = TRUE => #r.isAssociatedTo = 1
}

// Non esistono richieste riferite ad uno stesso driver che hanno la stessa data
fact DuplicatedRequestDriver{
	no d: DriverAccount, disj r1, r2: Request | r1.isAssociatedTo = d and r2.isAssociatedTo = d and r1.appointmentTime.year = r2.appointmentTime.year and r1.appointmentTime.month = r2.appointmentTime.month and r1.appointmentTime.day = r2.appointmentTime.day
}

//Non esistono richieste riferite ad uno stesso passeggero che hanno la stessa data 
fact DuplicatedRequestPassenger{
	no p: PassengerAccount, disj r1, r2: Request | r1.sender = p and r2.sender = p and r1.appointmentTime.year = r2.appointmentTime.year and r1.appointmentTime.month = r2.appointmentTime.month and r1.appointmentTime.day = r2.appointmentTime.day
}

//Functions
fun requestedRide[p: PassengerAccount] :
	set Ride { p.sends & Ride }

fun incompleteRequestedRide[p: PassengerAccount] :
	set Ride { requestedRide[p]  & {r: Ride | r.completed = FALSE} }
