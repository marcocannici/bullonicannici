module testMyTaxiService_1
open model

pred show [d: DriverAccount] {
	#d.takesCareOf > 1
}

run show for 10 but 1 PassengerAccount, 1 DriverAccount, 2 Account, 2 Taxi, 1 CityZone, 0 Notification, 2 Request
