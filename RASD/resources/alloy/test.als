module testMyTaxiService
open model

//TEST

//run testTaxiQueueZone for 10 but 2 DriverAccount, 2 Account, 0 Notification, 2 Taxi, 2 CityZone, 3 Coordinate
pred testTaxiQueueZone [ d: DriverAccount, t: Taxi, z1: CityZone, z2: CityZone ] {
	t.currentlyIn = z1 and d.currentlyDriving = t and #z2.driverQueue > 0 and #z1.driverQueue > 0 and z1 != z2
}

//run testPassengerQueueZone for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 1 Ride, 3 Coordinate
pred testPassengerQueueZone [p: PassengerAccount] {
	#incompleteRequestedRide[p] = 1 && #incompleteRequestedRide[p].isAssociatedTo = 0 
}

//run testMissingClientZone for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 2 Ride, 3 Coordinate
pred testMissingClientIncompletedRide [p: PassengerAccount] {
	#incompleteRequestedRide[p] > 0
}

//run testPassengerIncompletedRide for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 2 Ride, 3 Coordinate
pred testPassengerIncompletedRide [p: PassengerAccount] {
	#incompleteRequestedRide[p] > 0
}

//run testIncompleteDriverRequests for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Taxi, 1 CityZone, 3 Coordinate, 1 Strings, 2 Request
pred testIncompleteDriverRequests [d: DriverAccount] {
	#d.(~isAssociatedT)o > 1 and #{r:Request | d in r.isAssociatedTo && r.completed = FALSE} = 1 // se >1 dovrebbe fallire
}

//run testCompletedRequestDriver for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Taxi, 1 CityZone, 3 Coordinate, 1 Strings, 3 Request
pred testCompletedRequestDriver [d: DriverAccount] {
	#{r: Request | r.completed = FALSE && #r.isAssociatedTo = 1} < 2 // se = 2f allisce perchè impone che un driver abbia 2 richieste non complete associate
}

//run testDuplicatedRequestDriver for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 1 Taxi, 1 CityZone, 3 Coordinate, 3 Request, 2 Date
pred testDuplicatedRequestDriver [d: DriverAccount, r1: Request, r2: Request]{
	r1 != r2 and r1.isAssociatedTo = d and r2.isAssociatedTo = d
	r1.appointmentTime.year = r2.appointmentTime.year and
	r1.appointmentTime.month = r2.appointmentTime.month and
	r1.appointmentTime.day = r2.appointmentTime.day and
	r1.appointmentTime.hour = r2.appointmentTime.hour
}

//run testDuplicatedRequestPassenger for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 1 Taxi, 1 CityZone, 3 Coordinate, 3 Request, 2 Date
pred testDuplicatedRequestPassenger[p: PassengerAccount, r1: Request, r2: Request]{
	r1 != r2 and r1.~sends = p and r2.~sends = p and r1.appointmentTime.year = r2.appointmentTime.year and r1.appointmentTime.month = r2.appointmentTime.month
}

pred test{
	#Account > 1
}

run test for 2 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 1 Taxi, 1 CityZone, 2 Coordinate, 2 Request, 2 Date, 2 Strings
