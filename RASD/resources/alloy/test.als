module testMyTaxiService
open model

//TEST

//run testTaxiQueueZone for 10 but 2 DriverAccount, 2 Account, 0 Notification, 2 Taxi, 2 CityZone, 3 Coordinate
pred testTaxiQueueZone [ d: DriverAccount, t: Taxi, z1: CityZone, z2: CityZone ] {
	t.currentlyIn = z1 and d.currentlyDriving = t and #z2.driverQueue > 0 and #z1.driverQueue > 0 and z1 != z2
}

//run testPassengerQueueZone for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Reservation, 0 Taxi, 1 CityZone, 1 Ride, 3 Coordinate
pred testPassengerQueueZone [ p: PassengerAccount ] {
	#incompleteRequestedRide[p] > 0
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
	#d.takesCareOf > 1 and #{r:Request | d in r.isAssociatedTo && r.completed = FALSE} = 1 // se >1 dovrebbe fallire
}

//run testCompletedRequestDriver for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Taxi, 1 CityZone, 3 Coordinate, 1 Strings, 3 Request
pred testCompletedRequestDriver [d: DriverAccount] {
	#{r: Request | r.completed = FALSE && #r.isAssociatedTo = 1} = 2 //Falisce perchè impone che un driver abbia 2 richieste non complete associate
}

run testCompletedRequestDriver for 10 but 1 PassengerAccount, 1 DriverAccount,  2 Account, 0 Notification, 0 Taxi, 1 CityZone, 3 Coordinate, 1 Strings, 3 Request
